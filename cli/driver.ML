val root = valOf (OS.Process.getEnv "SPAN_ROOT");
val _ = use (root ^ "/.build/Span.Export/code/span.ML");

fun chars s = map (Span.ascii o IntInf.fromInt o Char.ord) (String.explode s);
fun text cs = String.implode (map (Char.chr o IntInf.toInt o Span.ordinal) cs);

fun read path =
  let
    val fd = if path = "-" then Posix.FileSys.stdin
      else Posix.FileSys.openf (path, Posix.FileSys.O_RDONLY, Posix.FileSys.O.flags [])
    fun close () = if path = "-" then () else Posix.IO.close fd
    fun loop total chunks =
      let
        val bytes = Posix.IO.readVec (fd, Int.min (65536, 1048577 - total))
        val count = Word8Vector.length bytes
      in
        if count = 0 then String.concat (List.rev chunks)
        else if total + count > 1048576 then raise Fail "input exceeds 1 MiB"
        else loop (total + count) (Byte.bytesToString bytes :: chunks)
      end
    val input = loop 0 [] handle exn => ((close () handle _ => ()); raise exn)
    val _ = close ()
  in
    input
  end;

fun write path text =
  let
    val bytes = Byte.stringToBytes text
    val pid = SysWord.toString (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))
    val prefix = OS.Path.concat (OS.Path.dir path, "." ^ OS.Path.file path ^ "." ^ pid ^ ".")
    val defaultMode = Posix.FileSys.S.flags [Posix.FileSys.S.irusr, Posix.FileSys.S.iwusr,
      Posix.FileSys.S.irgrp, Posix.FileSys.S.iwgrp, Posix.FileSys.S.iroth, Posix.FileSys.S.iwoth]
    val mode = Posix.FileSys.S.intersect [Posix.FileSys.ST.mode (Posix.FileSys.stat path),
      Posix.FileSys.S.flags [Posix.FileSys.S.irwxu, Posix.FileSys.S.irwxg, Posix.FileSys.S.irwxo]]
      handle exn as OS.SysErr (_, SOME error) =>
        if error = Posix.Error.noent then defaultMode else raise exn
    fun reserve n =
      if n = 128 then raise Fail "cannot reserve output file"
      else
        let
          val temporary = prefix ^ Int.toString n
        in
          (temporary, Posix.FileSys.createf
            (temporary, Posix.FileSys.O_WRONLY, Posix.FileSys.O.excl, mode))
        end handle exn as OS.SysErr (_, SOME error) =>
          if error = Posix.Error.exist then reserve (n + 1) else raise exn
    val (temporary, fd) = reserve 0
    val closed = ref false
    fun close () = (Posix.IO.close fd; closed := true)
    fun discard () =
      ((if !closed then () else close ()) handle _ => ();
       OS.FileSys.remove temporary handle _ => ())
    fun loop offset =
      if offset = Word8Vector.length bytes then ()
      else
        let
          val count = Posix.IO.writeVec (fd, Word8VectorSlice.slice (bytes, offset, NONE))
        in
          if count = 0 then raise Fail "output write made no progress" else loop (offset + count)
        end
  in
    (loop 0; close (); OS.FileSys.rename {old = temporary, new = path})
      handle exn => (discard (); raise exn)
  end;

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
        val ((ok, bytes), report) = Span.artifact (chars (read file))
      in
        if ok then
          (write destination (text bytes);
           output (true, report))
        else output (false, report)
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
