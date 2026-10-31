val root = valOf (OS.Process.getEnv "SPAN_ROOT");
val _ = use (root ^ "/.build/Span.Export/code/span.ML");

fun chars s = map (Span.ascii o IntInf.fromInt o Char.ord) (String.explode s);
fun text cs = String.implode (map (Char.chr o IntInf.toInt o Span.ordinal) cs);

fun read path =
  let
    val stream = if path = "-" then TextIO.stdIn else TextIO.openIn path
    val text = TextIO.inputN (stream, 1048577)
    val _ = if path = "-" then () else TextIO.closeIn stream
  in
    if size text > 1048576 then raise Fail "input exceeds 1 MiB" else text
  end;

fun write path text =
  let
    val stream = BinIO.openOut path
    val _ = BinIO.output (stream, Byte.stringToBytes text)
  in BinIO.closeOut stream end;

fun output (ok, message) =
  (TextIO.output (if ok then TextIO.stdOut else TextIO.stdErr, text message);
   OS.Process.exit (if ok then OS.Process.success else OS.Process.failure));

fun usage () =
  (TextIO.output (TextIO.stdOut,
    "usage: span assemble file [-o binary]\n       span trace file\n       span list file\n       span run file [fuel]\n       span disassemble binary\n\nuse - to read standard input\n");
   OS.Process.exit OS.Process.success);

fun run args =
  case args of
    [] => usage ()
  | ["--help"] => usage ()
  | ["disassemble", file] => output (Span.disassemble (chars (read file)))
  | ["assemble", file, "-o", destination] =>
      let
        val input = chars (read file)
        val (ok, bytes) = Span.binary input
      in
        if ok then
          (write destination (text bytes);
           output (Span.process [chars "assemble"] input))
        else output (false, bytes)
      end
  | ["run", file] => output (Span.process (map chars ["run", "4096"]) (chars (read file)))
  | ["run", file, fuel] => output (Span.process (map chars ["run", fuel]) (chars (read file)))
  | [mode, file] =>
      if List.exists (fn x => x = mode) ["assemble", "trace", "list"] then
        output (Span.process [chars mode] (chars (read file)))
      else raise Fail "unknown command, use span --help"
  | _ => raise Fail "invalid arguments, use span --help";

fun main () = run (CommandLine.arguments ())
  handle exn =>
    (TextIO.output (TextIO.stdErr, "span: " ^ General.exnMessage exn ^ "\n");
     OS.Process.exit OS.Process.failure);
