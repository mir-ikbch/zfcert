let contains text fragment =
  let rec loop index =
    index + String.length fragment <= String.length text
    && (String.sub text index (String.length fragment) = fragment
        || loop (index + 1))
  in
  loop 0

let expect_error ?line fragments evaluate =
  match evaluate () with
  | _ -> failwith "input accepted an invalid script"
  | exception Proof_session.Proof_error (actual_line, message) ->
      Option.iter
        (fun expected ->
           if actual_line <> expected then
             failwith (Printf.sprintf "input error line: expected %d, got %d (%s)"
               expected actual_line message))
        line;
      List.iter
        (fun fragment ->
           if not (contains message fragment) then
             failwith ("input error missing " ^ fragment ^ ": " ^ message))
        fragments

let run () =
  let directory = Filename.temp_file "zfcert-input-" "" in
  Sys.remove directory;
  Unix.mkdir directory 0o700;
  let directory = Unix.realpath directory in
  let subdirectory = Filename.concat directory "lib" in
  Unix.mkdir subdirectory 0o700;
  let files = ref [] in
  let path name = Filename.concat directory name in
  let write name contents =
    let filename = path name in
    files := filename :: !files;
    let channel = open_out_bin filename in
    Fun.protect ~finally:(fun () -> close_out_noerr channel)
      (fun () -> output_string channel contents)
  in
  Fun.protect
    ~finally:(fun () ->
      List.iter Sys.remove !files;
      Unix.rmdir subdirectory;
      Unix.rmdir directory)
    (fun () ->
      let filename = path "main.zfp" in
      let check =
        Proof_session.check_script ~filename ~load_input:Native_input.load
      in
      let analyze =
        Proof_session.analyze_script ~filename ~load_input:Native_input.load
      in
      let verified expected script =
        let state = check script in
        if Proof_session.theorem_name state <> expected then
          failwith "input returned the wrong theorem";
        match Proof_session.certificate_rules state with
        | Some (_ :: _) -> ()
        | _ -> failwith "input proof was not certified by the kernel"
      in
      write "base.zfp"
        "alias same x := x = x.\n\
         choose empty Hempty from empty_set.\n\
         theorem prior : forall x, same x.\nintro x.\nrefl.\nqed.";
      write "lib/nested.zfp" "input \"../base.zfp\".";
      verified "use_prior"
        "input \"lib/nested.zfp\".\n\
         theorem use_prior : forall x, same x.\nexact prior.\nqed.";
      verified "use_choice"
        "input \"base.zfp\".\n\
         theorem use_choice : forall x, not (x in empty).\nexact Hempty.\nqed.";
      verified "alias_imported_choice"
        "input \"base.zfp\".\n\
         alias empty_has_no_members := forall x, not (x in empty).\n\
         theorem alias_imported_choice : empty_has_no_members.\n\
         put Hempty.\nexact Hempty.\nqed.";
      verified "prior" "input \"base.zfp\".";
      verified "prior" (Printf.sprintf "input %S." (path "base.zfp"));
      write "root-context.zfp"
        "theorem from_root : forall x, root_alias x.\nintro x.\nrefl.\nqed.";
      verified "from_root"
        "alias root_alias x := x = x.\ninput \"root-context.zfp\".";
      write "tactics.zfp" "intro x.\nrefl.";
      verified "split_proof"
        "theorem split_proof : forall x, x = x.\ninput \"tactics.zfp\".\nqed.";
      write "refl.zfp" "refl.";
      verified "repeated"
        "theorem repeated : forall x, (x = x and x = x).\n\
         intro x.\nsplit.\ninput \"refl.zfp\".\ninput \"refl.zfp\".\nqed.";
      write "empty.zfp" "(* no declarations *)";
      verified "prior" "input \"empty.zfp\".\ninput \"base.zfp\".";
      let unusual = "日本語 # (*file*).zfp" in
      write unusual "alias unusual x := x = x.";
      verified "quoted_path"
        ("input \"" ^ unusual ^ "\".\n\
          theorem quoted_path : forall x, unusual x.\nintro x.\nrefl.\nqed.");
      write "quote\"and\\slash.zfp" "alias escaped x := x = x.";
      verified "escaped_path"
        "input \"quote\\\"and\\\\slash.zfp\".\n\
         theorem escaped_path : forall x, escaped x.\nintro x.\nrefl.\nqed.";
      let state, has_qed = analyze
        "input \"base.zfp\".\n\
         theorem interactive : forall x, same x.\nintro x." in
      if has_qed || List.length (Proof_session.goals state) <> 1 then
        failwith "input did not preserve interactive proof state";
      write "bad.zfp" "theorem bad : forall x, x = x.\nintro x.\nbogus.\nqed.";
      expect_error ~line:2 ["bad.zfp:3"; "Unknown tactic"]
        (fun () -> check "# root\ninput \"bad.zfp\".");
      write "unproved.zfp" "theorem unproved : false.\nqed.";
      expect_error ~line:1 ["unproved.zfp:2"; "unresolved goals"]
        (fun () -> check
          "input \"unproved.zfp\".\ntheorem invalid : false.\nexact unproved.\nqed.");
      write "lib/bad-nested.zfp" "# nested\ninput \"../bad.zfp\".";
      expect_error ~line:3 ["bad.zfp:3"; "Unknown tactic"]
        (fun () -> check "# root\n\ninput \"lib/bad-nested.zfp\".");
      expect_error ~line:4 ["Unknown tactic"]
        (fun () -> check
          "input \"base.zfp\".\ntheorem bad : forall x, x = x.\nintro x.\nbogus.");
      write "parse-error.zfp" "# comment\n(* unterminated";
      expect_error ~line:2 ["parse-error.zfp:2"; "Unterminated block comment"]
        (fun () -> check "\ninput \"parse-error.zfp\".");
      write "unfinished.zfp" "theorem unfinished : forall x, x = x.\nintro x.";
      expect_error ~line:1 ["unfinished.zfp:2"; "unresolved goals"]
        (fun () -> check "input \"unfinished.zfp\".");
      expect_error ~line:2 ["missing.zfp"]
        (fun () -> check "\ninput \"missing.zfp\".");
      write "lib/missing.zfp" "\ninput \"not-found.zfp\".";
      expect_error ~line:1 ["lib/missing.zfp:2"; "not-found.zfp"]
        (fun () -> check "input \"lib/missing.zfp\".");
      write "a.zfp" "input \"b.zfp\".";
      write "b.zfp" "input \"a.zfp\".";
      expect_error ["Circular input"; "a.zfp"] (fun () -> check "input \"a.zfp\".");
      write "self.zfp" "input \"lib/../self.zfp\".";
      expect_error ["Circular input"; "self.zfp"] (fun () -> check "input \"self.zfp\".");
      let symlink = path "link.zfp" in
      Unix.symlink (path "linked.zfp") symlink;
      files := symlink :: !files;
      write "linked.zfp" "input \"link.zfp\".";
      expect_error ["Circular input"; "linked.zfp"]
        (fun () -> check "input \"linked.zfp\".");
      List.iter
        (fun script -> expect_error ~line:1 [] (fun () -> check script))
        ["input base.zfp."; "input \"\"."; "input \"base.zfp\" extra.";
         "input \"base.zfp\""; "input \"base.zfp.";
         "input \"base\nzfp\"."];
      expect_error ~line:1 ["input"]
        (fun () -> Proof_session.check_script "input \"base.zfp\".");
      expect_error ~line:1 ["The proof script is empty."]
        (fun () -> Proof_session.check_script "# only comments\n\n");
      let browser_result = Web_api.check "input \"base.zfp\"." in
      if not (contains browser_result "\"ok\":false") then
        failwith "Browser input without a loader was accepted";
      Printf.printf "Input file tests passed.\n%!")
