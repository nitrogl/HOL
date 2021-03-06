(*---------------------------------------------------------------------------
                An ML script for building HOL
 ---------------------------------------------------------------------------*)

structure build =
struct

open buildutils
datatype phase = Initial | Bare | Full

(* utilities *)

  fun main () = let

    val phase = ref Initial


    open buildutils

(* ----------------------------------------------------------------------
    Analysing the command-line
   ---------------------------------------------------------------------- *)

fun kmod kernelspec = let
  (* use the experimental kernel? Depends on the command-line and the
     compiler version... *)
  val version_string_w1 =
      hd (String.tokens Char.isSpace PolyML.Compiler.compilerVersion)
      handle Empty => ""
  val compiler_number =
      Real.floor (100.0 * valOf (Real.fromString version_string_w1))
      handle Option => 0
in
  if kernelspec <> "-expk" andalso compiler_number < 530 then
    (warn "*** Using the experimental kernel (standard kernel requires \
          \Poly/ML 5.3 or\n*** higher)";
     "-expk")
  else
    kernelspec
end


val {cmdline,build_theory_graph,do_selftests,SRCDIRS} = process_cline kmod

open Systeml;

fun which_hol () =
  case !phase of
    Initial => [POLY, "--poly_not_hol"]
  | Bare => [fullPath [HOLDIR, "bin", "hol.builder0"]]
  | Full => [fullPath [HOLDIR, "bin", "hol.builder"]]

fun aug_systeml proc args = let
  open Posix.Process
  val env' =
      "SELFTESTLEVEL="^Int.toString do_selftests :: Posix.ProcEnv.environ()
in
  case fork() of
    NONE => (exece(proc,proc::args,env')
             handle _ => die ("Exece of "^proc^" failed"))
  | SOME cpid => let
      val (_, result) = waitpid(W_CHILD cpid, [])
    in
      result
    end
end


val Holmake = let
  fun extras() = "--poly" :: which_hol()
  fun isSuccess Posix.Process.W_EXITED = true
    | isSuccess _ = false
  fun analysis hmstatus = let
    open Posix.Process
  in
    case hmstatus of
      W_EXITSTATUS w8 => "exited with code "^Word8.toString w8
    | W_EXITED => "exited normally???"
    | W_SIGNALED sg => "with signal " ^
                       SysWord.toString (Posix.Signal.toWord sg)
    | W_STOPPED sg => "stopped with signal " ^
                      SysWord.toString (Posix.Signal.toWord sg)
  end
in
  buildutils.Holmake aug_systeml isSuccess extras analysis do_selftests
end

(* create a symbolic link - Unix only *)
fun link b s1 s2 =
    Posix.FileSys.symlink {new = s2, old = s1}
    handle OS.SysErr (s, _) =>
           die ("Unable to link old file "^quote s1^" to new file "
                ^quote s2^": "^s)

fun symlink_check() =
    if OS = "winNT" then
      die "Sorry; symbolic linking isn't available under Windows NT"
    else link
val default_link = if OS = "winNT" then cp else link

(*---------------------------------------------------------------------------
        Transport a compiled directory to another location. The
        symlink argument says whether this is via a symbolic link,
        or by copying. The ".uo", ".ui", ".so", ".xable" and ".sig"
        files are transported.
 ---------------------------------------------------------------------------*)

fun upload ((src, regulardir), target, symlink) =
    if regulardir = 0 then
      (print ("Uploading files to "^target^"\n");
       map_dir (transfer_file symlink target) src)
      handle OS.SysErr(s, erropt) =>
             die ("OS error: "^s^" - "^
                  (case erropt of SOME s' => OS.errorMsg s'
                                | _ => ""))
    else if do_selftests >= regulardir then
      print ("Self-test directory "^src^" built successfully.\n")
    else ()

(*---------------------------------------------------------------------------
    For each element in SRCDIRS, build it, then upload it to SIGOBJ.
    This allows us to have the build process only occur w.r.t. SIGOBJ
    (thus requiring only a single place to look for things).
 ---------------------------------------------------------------------------*)

fun make_exe (name:string) (POLY : string) (target:string) : unit = let
  val _ = print ("Building "^target^"\n")
  val dir = OS.FileSys.getDir()
 in
   OS.FileSys.chDir (fullPath [HOLDIR, "tools-poly"]);
   Systeml.system_ps (POLY ^ " < " ^ name);
   Poly_link {exe = fullPath [Systeml.HOLDIR, "bin", target],
              obj = target ^ ".o"};
   OS.FileSys.chDir dir
 end

fun buildDir symlink s =
  if #1 s = fullPath [HOLDIR, "bin/hol.bare"] then phase := Bare
  else if #1 s = fullPath [HOLDIR, "bin/hol"] then phase := Full
  else
    (build_dir Holmake do_selftests s; upload(s,SIGOBJ,symlink))

fun build_src symlink = List.app (buildDir symlink) SRCDIRS

fun build_hol symlink = let
in
  clean_sigobj();
  setup_logfile();
  build_src symlink
    handle SML90.Interrupt => (finish_logging false; die "Interrupted");
  finish_logging true;
  make_buildstamp();
  build_help build_theory_graph;
  print "\nHol built successfully.\n"
end


(*---------------------------------------------------------------------------
       Get rid of compiled code and dependency information.
 ---------------------------------------------------------------------------*)

val check_againstB = check_against EXECUTABLE
val _ = check_againstB "tools-poly/smart-configure.sml"
val _ = check_againstB "tools-poly/configure.sml"
val _ = check_againstB "tools-poly/build.sml"
val _ = check_againstB "tools/Holmake/Systeml.sig"

val _ = let
  val fP = fullPath
  open OS.FileSys
  val hmake = fP [HOLDIR,"bin",xable_string "Holmake"]
in
  if access(hmake, [A_READ, A_EXEC]) then
    (app_sml_files (check_against hmake)
                   {dirname = fP [HOLDIR, "tools-poly", "Holmake"]};
     app_sml_files (check_against hmake)
                   {dirname = fP [HOLDIR, "tools", "Holmake"]})
  else
    die ("No Holmake executable in " ^ fP [HOLDIR, "bin"])
end





in
    case cmdline of
      []            => build_hol default_link
    | ["-symlink"]  => build_hol (symlink_check()) (* w/ symbolic linking *)
    | ["-nosymlink"]=> build_hol cp
    | ["-dir",path] => buildDir cp (path, 0)
    | ["-dir",path,
       "-symlink"]  => buildDir (symlink_check()) (path, 0)
    | ["symlink"]   => build_hol (symlink_check())
    | ["nosymlink"] => build_hol cp
    | ["small"]     => build_hol mv
    | otherwise     => warn help_mesg
  end
end (* struct *)
