(* The gate suite. Every check here pins something the paper states.

     Test_projection  the projection ⌊·⌋ of an I_S^T run is exactly the T
                      machine's own run (lem:bisim), and the extracted call and
                      return points are the paper's L_call and L_ret
     Test_calc_pe     the segmentation the specializer derives from the
                      interpreter text is the paper's factorization table
                      (tab:macro), and the residual tabulates only those cuts
                      (lem:decomposition)
     Test_gen_calc    the stored specialized analyzer (lib_gen/, machine-written
                      by staging/) computes what the in-process one computes
     Test_corpus      over the whole program corpus, for every argument case:
                      the concrete T machine agrees with the declared value,
                      I_S^T agrees with the T machine, the base analyzer is
                      sound, and the specialized analyzer is sound and EQUALS
                      the base

   Each module exposes [run : unit -> unit] and prints its own checks; a failing
   check aborts the run at once (via [Test_util.check]).

   `dune test` truncates long output. To see every check, run the binary:
   ./_build/default/tests/test_main.exe *)

let () =
  Test_projection.run ();
  Test_calc_pe.run ();
  Test_gen_calc.run ();
  Test_corpus.run ();
  print_endline "all tests passed"
