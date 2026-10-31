import itertools
from pathlib import Path
import random
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
CHECKS = 0


def check(condition, message):
    global CHECKS
    if not condition:
        raise AssertionError(message)
    CHECKS += 1


def cli(*args, text=None, ok=True):
    result = subprocess.run(
        [str(ROOT / "span"), *map(str, args)],
        input=text,
        text=True,
        capture_output=True,
        timeout=90,
        cwd=ROOT,
    )
    check((result.returncode == 0) == ok, (args, result.stdout, result.stderr))
    return result.stdout if ok else result.stderr


def source(program):
    lines = []
    for i, (op, target) in enumerate(program):
        lines.append(f"label b{i}")
        lines.append(f"{op} b{target}" if op in ("jmp", "jz") else op)
    return "\n".join(lines) + "\n"


def layouts(program):
    branches = [i for i, (op, _) in enumerate(program) if op in ("jmp", "jz")]
    for flags in itertools.product((False, True), repeat=len(branches)):
        wide = dict(zip(branches, flags))
        positions = [0]
        for i in range(len(program)):
            positions.append(positions[-1] + (3 if wide.get(i) else 2 if i in wide else 1))
        if all(
            -(32768 if wide[i] else 128)
            <= positions[program[i][1]] - positions[i + 1]
            < (32768 if wide[i] else 128)
            for i in branches
        ):
            yield positions[-1]


def interpret(program, fuel):
    pc, acc = 0, 0
    for _ in range(fuel):
        if pc >= len(program) or program[pc][0] == "halt":
            break
        op, target = program[pc]
        if op == "inc":
            acc += 1
        elif op == "dec":
            acc = max(0, acc - 1)
        if op == "jmp" or op == "jz" and acc == 0:
            pc = target
        else:
            pc += 1
    return pc, acc


def decode(data):
    rows, at = [], 0
    while at < len(data):
        start, op = at, data[at]
        at += 1
        if op in (16, 17, 18, 19):
            length = 2 if op < 18 else 3
            payload = int.from_bytes(data[at : at + length - 1], "little")
            at += length - 1
            rows.append((start, at, op, payload - (128 if length == 2 else 32768)))
        else:
            check(op in (0, 1, 2, 3), "invalid opcode")
            rows.append((start, at, op, None))
    return rows


def verify(program, data):
    rows = decode(data)
    check(len(rows) == len(program), "instruction count changed")
    for (op, target), (_, end, opcode, displacement) in zip(program, rows):
        if op in ("jmp", "jz"):
            check(opcode in ((16, 18) if op == "jmp" else (17, 19)), "branch kind changed")
            check(end + displacement == rows[target][0], "branch destination changed")
        else:
            check(opcode == {"nop": 0, "inc": 1, "dec": 2, "halt": 3}[op], "opcode changed")
    check(len(data) == min(layouts(program)), "layout is not minimum")
    return rows


def main():
    check("usage:" in cli("--help"), "help missing")
    check("135 bytes" in cli("assemble", "examples/cascade.span"), "cascade size")
    trace = cli("trace", "examples/cascade.span")
    check("pass 0  133 bytes  widen [1]" in trace, "first cascade pass")
    check("pass 1  134 bytes  widen [0]" in trace, "second cascade pass")
    check("pass 2  135 bytes  widen []" in trace, "fixed point missing")
    check("halted  pc=8  acc=0" in cli("run", "examples/countdown.span"), "countdown execution")
    check("fuel exhausted" in cli("run", "examples/countdown.span", "1"), "fuel limit")
    check("fuel exhausted  pc=0  acc=0" in cli("run", "-", "5", text="label loop\njmp loop"), "self branch")
    for text, message in [
        ("jmp nowhere", "undefined label"),
        ("label a\nlabel a", "duplicate label"),
        ("jmp end\nlabel end", "after the final instruction"),
        ("pad -1", "invalid padding"),
        ("pad 65537", "invalid padding"),
        ("pad 65536\nnop", "exceeds 65536"),
        ("jmp", "invalid instruction"),
        ("halt extra", "invalid instruction"),
        ("label \x1b[31m", "printable ASCII"),
    ]:
        check(message in cli("assemble", "-", text=text, ok=False), message)
    check("16-bit range" in cli("assemble", "examples/overflow.span", ok=False), "overflow accepted")
    check("65536 instructions, 65536 bytes" in cli("assemble", "-", text="nop\n" * 65536), "maximum line count")
    check("invalid instruction at line 4097" in cli("assemble", "-", text="nop\n" * 4096 + "invalid\npad -1", ok=False), "first parse error changed")
    check("undefined label first" in cli("assemble", "-", text="pad 3\njmp first\njmp second", ok=False), "first resolution error changed")
    for padding, width in [(127, 2), (128, 3), (32767, 3)]:
        report = cli("assemble", "-", text=f"jmp end\npad {padding}\nlabel end\nhalt")
        check(f"{padding + width + 1} bytes" in report, "forward range boundary")
    for padding, width in [(126, 2), (127, 3), (32765, 3)]:
        report = cli("assemble", "-", text=f"label start\npad {padding}\njmp start\nhalt")
        check(f"{padding + width + 1} bytes" in report, "backward range boundary")
    check("16-bit range" in cli("assemble", "-", text="label start\npad 32766\njmp start\nhalt", ok=False), "negative overflow accepted")
    rng = random.Random(0x5350414E)
    with tempfile.TemporaryDirectory() as directory:
        out = Path(directory) / "program.bin"
        for case in range(36):
            length = rng.randrange(8, 180)
            program = [(rng.choice(("nop", "inc", "dec")), None) for _ in range(length)]
            for i in rng.sample(range(length - 1), rng.randrange(1, 7)):
                program[i] = (rng.choice(("jmp", "jz")), rng.randrange(length))
            program[-1] = ("halt", None)
            text = source(program)
            cli("assemble", "-", "-o", out, text=text)
            rows = verify(program, out.read_bytes())
            pc, acc = interpret(program, 256)
            expected = rows[pc][0] if pc < length else len(out.read_bytes())
            report = cli("run", "-", "256", text=text)
            check(f"pc={expected}  acc={acc}\n" in report, f"execution mismatch in case {case}")
        report = cli("assemble", "examples/countdown.span", "-o", out)
        check(report == cli("assemble", "examples/countdown.span"), "binary report changed")
        check(out.read_bytes() == bytes([1, 1, 1, 2, 17, 130, 16, 123, 3]), "binary output")
        check("jmp.8 -5" in cli("disassemble", out), "binary disassembly")
        out.write_bytes(bytes([18, 0]))
        check("invalid encoding" in cli("disassemble", out, ok=False), "truncated encoding accepted")
        out.write_bytes(bytes([255]))
        check("invalid encoding" in cli("disassemble", out, ok=False), "unknown opcode accepted")
        out.write_bytes(b"preserve")
        error = cli("assemble", "-", "-o", out, text="jmp missing", ok=False)
        check(error == cli("assemble", "-", text="jmp missing", ok=False), "binary error changed")
        check(out.read_bytes() == b"preserve", "failed assembly clobbered output")
        cli("assemble", "-", "-o", out, text="")
        check(out.read_bytes() == b"", "empty binary output")
    print(f"{CHECKS} checks passed, including 36 exhaustive layout comparisons")


if __name__ == "__main__":
    main()
