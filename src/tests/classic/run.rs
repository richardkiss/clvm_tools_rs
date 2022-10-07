use std::collections::HashSet;
use std::path::PathBuf;

use clvmr::allocator::Allocator;

use crate::classic::clvm::__type_compatibility__::Stream;
use crate::classic::clvm_tools::cmds::{launch_tool, OpcConversion, OpdConversion, TConversion};
use crate::classic::clvm_tools::sha256tree::sha256tree;

use crate::compiler::sexp::decode_string;

fn do_basic_brun(args: &Vec<String>) -> String {
    let mut s = Stream::new(None);
    launch_tool(&mut s, args, &"run".to_string(), 0);
    return s.get_value().decode();
}

fn do_basic_run(args: &Vec<String>) -> String {
    let mut s = Stream::new(None);
    launch_tool(&mut s, args, &"run".to_string(), 2);
    return s.get_value().decode();
}

#[test]
fn basic_run_test() {
    assert_eq!(
        do_basic_run(&vec!("run".to_string(), "(mod (A B) (+ A B))".to_string())).trim(),
        "(+ 2 5)".to_string()
    );
}

#[test]
fn add_1_test() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(opt (com (q . (+ 6 55))))".to_string()
        ))
        .trim(),
        "(q . 61)".to_string()
    );
}

#[test]
fn div_test() {
    assert_eq!(
        do_basic_run(&vec!("run".to_string(), "(mod (X) (/ X 10))".to_string())).trim(),
        "(f (divmod 2 (q . 10)))".to_string()
    );
}

#[test]
fn brun_y_1_test() {
    let testpath = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut sym_path = testpath.clone();
    sym_path.push("resources/tests/stage_2/brun-y-1.sym");
    assert_eq!(
        do_basic_brun(
            &vec!(
                "brun".to_string(),
                "-y".to_string(),
                sym_path.into_os_string().into_string().unwrap(),
                "(a (q . (a 2 (c 2 (c 5 (q . ()))))) (c (q . (a (i (= 5 (q . 1)) (q . (q . 1)) (q . (* 5 (a 2 (c 2 (c (- 5 (q . 1)) (q . ()))))))) 1)) 1))".to_string(),
                "(10)".to_string()
            )
        ).trim(),
        indoc! {"0x375f00
            
            (\"fact\" 10) => 0x375f00
            
            (\"fact\" 9) => 0x058980
            
            (\"fact\" 8) => 0x009d80
            
            (\"fact\" 7) => 5040
            
            (\"fact\" 6) => 720
            
            (\"fact\" 5) => 120
            
            (\"fact\" 4) => 24
            
            (\"fact\" 3) => 6
            
            (\"fact\" 2) => 2
            
            (\"fact\" 1) => 1"}
    );
}

#[test]
fn brun_v_test() {
    assert_eq!(
        do_basic_brun(&vec!(
            "brun".to_string(),
            "-v".to_string(),
            "(a (q + (q . 3) (q . 5)) 1)".to_string()
        ))
        .trim(),
        indoc! {"8
            
            (a 2 3) [((a (q 16 (q . 3) (q . 5)) 1))] => 8
            
            3 [((a (q 16 (q . 3) (q . 5)) 1))] => ()
            
            2 [((a (q 16 (q . 3) (q . 5)) 1))] => (a (q 16 (q . 3) (q . 5)) 1)
            
            (a (q 16 (q . 3) (q . 5)) 1) [()] => 8
            
            1 [()] => ()
            
            (q 16 (q . 3) (q . 5)) [()] => (+ (q . 3) (q . 5))
            
            (+ (q . 3) (q . 5)) [()] => 8
            
            (q . 5) [()] => 5
            
            (q . 3) [()] => 3"}
    );
}

#[test]
fn brun_constant_test() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defconstant X 3) X)".to_string()
        ))
        .trim(),
        "(q . 3)".to_string()
    );
}

#[test]
fn at_capture_destructure_1() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod (A (@ Z (B C)) D) A)".to_string()
        ))
        .trim(),
        "2"
    );
}

#[test]
fn at_capture_destructure_2() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod (A (@ Z (B C)) D) Z)".to_string()
        ))
        .trim(),
        "5"
    );
}

#[test]
fn at_capture_destructure_3() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod (A (@ Z (B C)) D) B)".to_string()
        ))
        .trim(),
        "9"
    );
}

#[test]
fn at_capture_destructure_4() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod (A (@ Z (B C)) D) C)".to_string()
        ))
        .trim(),
        "21"
    );
}

#[test]
fn at_capture_destructure_5() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod (A (@ Z (B C)) D) D)".to_string()
        ))
        .trim(),
        "11"
    );
}

#[test]
fn at_capture_inline_1() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defun-inline F (@ pt (X Y)) X) (F 97 98))".to_string()
        ))
        .trim(),
        "(q . 97)"
    );
}

#[test]
fn at_capture_inline_2() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defun-inline F (@ pt (X Y)) Y) (F 97 98))".to_string()
        ))
        .trim(),
        "(q . 98)"
    );
}

#[test]
fn at_capture_inline_3() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defun-inline F (@ pt (X Y)) pt) (F (+ 117 1) (+ 98 1)))".to_string()
        ))
        .trim(),
        "(q 118 99)"
    );
}

#[test]
fn at_capture_inline_4() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defun-inline F (A (@ pt (X Y))) (list (list A X Y) pt)) (F 115 (list 99 77)))".to_string()
        ))
            .trim(),
        "(q (115 99 77) (99 77))"
    );
}

#[test]
fn inline_destructure_1() {
    assert_eq!(
        do_basic_run(&vec!(
            "run".to_string(),
            "(mod () (defun-inline F ((A . B)) (+ A B)) (F (c 3 7)))".to_string()
        ))
        .trim(),
        "(q . 10)"
    );
}

#[test]
fn test_forms_of_destructuring_allowed_by_classic_1() {
    assert_eq!(
        do_basic_run(&vec![
            "run".to_string(),
            "(mod (A) (defun-inline foo (X Y . Z) (i X Y . Z)) (foo A 2 3))".to_string()
        ])
        .trim(),
        "(i 2 (q . 2) (q . 3))"
    );
}

#[test]
fn test_compile_file_1() {
    let program = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "(mod () (compile-file foo secret_number.cl) foo)".to_string(),
    ])
    .trim()
    .to_string();
    let run_result = do_basic_brun(&vec!["brun".to_string(), program, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(run_result, "(+ 2 (q . 19))");
}

#[test]
fn test_embed_file_2() {
    let program = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "(mod () (embed-file testhex hex hex-embed-01.hex) testhex)".to_string(),
    ])
    .trim()
    .to_string();
    let run_result = do_basic_brun(&vec!["brun".to_string(), program, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(run_result, "(65 66 67)");
}

#[test]
fn test_compile_file_3() {
    let program = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "(mod () (include *standard-cl-21*) (compile-file foo secret_number.cl) foo)".to_string(),
    ])
    .trim()
    .to_string();
    let run_result = do_basic_brun(&vec!["brun".to_string(), program, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(run_result, "(+ 2 (q . 19))");
}

#[test]
fn test_embed_file_4() {
    let program = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "(mod () (include *standard-cl-21*) (embed-file testhex hex hex-embed-01.hex) testhex)"
            .to_string(),
    ])
    .trim()
    .to_string();
    let run_result = do_basic_brun(&vec!["brun".to_string(), program, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(run_result, "(65 66 67)");
}

#[test]
fn test_embed_file_5() {
    let program = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "(mod () (embed-file testsexp sexp embed.sexp) testsexp)".to_string(),
    ])
    .trim()
    .to_string();
    let run_result = do_basic_brun(&vec!["brun".to_string(), program, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(run_result, "(lsh 24 25)");
}

#[test]
fn test_embed_file_6() {
    let program = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "(mod () (include *standard-cl-21*) (embed-file testsexp sexp embed.sexp) testsexp)"
            .to_string(),
    ])
    .trim()
    .to_string();
    let run_result = do_basic_brun(&vec!["brun".to_string(), program, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(run_result, "(lsh 24 25)");
}

#[test]
fn test_embed_file_7() {
    let program = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "(mod () (embed-file hello bin hello.bin) hello)".to_string(),
    ])
    .trim()
    .to_string();
    let run_result = do_basic_brun(&vec!["brun".to_string(), program, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(run_result, "\"hello\"");
}

#[test]
fn test_embed_file_8() {
    let program = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "(mod () (include *standard-cl-21*) (embed-file hello bin hello.bin) hello)".to_string(),
    ])
    .trim()
    .to_string();
    let run_result = do_basic_brun(&vec!["brun".to_string(), program, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(run_result, "\"hello\"");
}

#[test]
fn test_embed_file_9() {
    let program = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "(mod () (include *standard-cl-21*) (embed-file hello bin hello.bin) (sha256 (sha256 hello)))".to_string(),
    ])
        .trim()
        .to_string();
    let run_result = do_basic_brun(&vec!["brun".to_string(), program, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(
        run_result,
        "0x9595c9df90075148eb06860365df33584b75bff782a510c6cd4883a419833d50"
    );
}

fn run_dependencies(filename: &str) -> HashSet<String> {
    let result_text = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "-M".to_string(),
        filename.to_owned(),
    ])
    .trim()
    .to_string();

    let mut dep_set = HashSet::new();
    for l in result_text.lines() {
        if let Some(suffix_start) = l.find("resources/tests") {
            let copied_suffix: Vec<u8> = l.as_bytes().iter().skip(suffix_start).copied().collect();
            dep_set.insert(decode_string(&copied_suffix));
        } else {
            panic!("file {} isn't expected", l);
        }
    }

    dep_set
}

#[test]
fn test_include_non_strict_no_fail() {
    let result = do_basic_run(&vec![
        "run".to_string(),
        "(mod () (defun-inline foo (X) (+ X1 1)) (foo 3))".to_string(),
    ])
    .trim()
    .to_string();

    assert_eq!(result.find("Unknown variable reference X1").is_none(), true);
}

#[test]
fn test_get_dependencies_1() {
    let dep_set = run_dependencies("resources/tests/singleton_top_layer.clvm");

    let mut expect_set = HashSet::new();
    expect_set.insert("resources/tests/condition_codes.clvm".to_owned());
    expect_set.insert("resources/tests/curry-and-treehash.clinc".to_owned());
    expect_set.insert("resources/tests/singleton_truths.clib".to_owned());

    assert_eq!(dep_set, expect_set);
}

#[test]
fn test_get_dependencies_2() {
    let dep_set = run_dependencies("resources/tests/test_treehash_constant.cl");

    let mut expect_set = HashSet::new();
    expect_set.insert("resources/tests/sha256tree.clib".to_owned());
    expect_set.insert("resources/tests/secret_number.cl".to_owned());
    expect_set.insert("resources/tests/test_sub_include.cl".to_owned());
    assert_eq!(dep_set, expect_set);
}

#[test]
fn test_treehash_constant() {
    let result_text = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "resources/tests/test_treehash_constant.cl".to_string(),
    ])
    .trim()
    .to_string();
    let result_hash = do_basic_brun(&vec!["brun".to_string(), result_text, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(
        result_hash,
        "0x34380f2097b86970818f8b026b68135d665babc5fda5afe577f86d51105e08b5"
    );
}

#[test]
fn test_treehash_constant_2() {
    let result_text = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "resources/tests/test_treehash_constant_2.cl".to_string(),
    ])
    .trim()
    .to_string();
    let result_hash = do_basic_brun(&vec!["brun".to_string(), result_text, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(
        result_hash,
        "0xe2954b5f459d1cffff293498f8263c961890a06fe28d6be1a0f08412164ced80"
    );
}

#[test]
fn test_treehash_constant_21() {
    let result_text = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "resources/tests/test_treehash_constant_21.cl".to_string(),
    ])
    .trim()
    .to_string();
    let result_hash = do_basic_brun(&vec!["brun".to_string(), result_text, "()".to_string()])
        .trim()
        .to_string();
    assert_eq!(
        result_hash,
        "0x34380f2097b86970818f8b026b68135d665babc5fda5afe577f86d51105e08b5"
    );
}

#[test]
fn test_treehash_constant_21_2() {
    let mut allocator = Allocator::new();
    let expected_hash = "0xe2954b5f459d1cffff293498f8263c961890a06fe28d6be1a0f08412164ced80";

    let result_text = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "resources/tests/test_treehash_constant_21_2.cl".to_string(),
    ])
    .trim()
    .to_string();
    let result_hash = do_basic_brun(&vec!["brun".to_string(), result_text, "()".to_string()])
        .trim()
        .to_string();

    assert_eq!(result_hash, expected_hash);

    // Test that run matches
    let compiled = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "resources/tests/secret_number2.cl".to_string(),
    ])
    .trim()
    .to_string();
    let hexed = OpcConversion {}.invoke(&mut allocator, &compiled).unwrap();
    let sexp = OpdConversion {}
        .invoke(&mut allocator, &hexed.rest())
        .unwrap();
    let tree_hash = format!("0x{}", sha256tree(&mut allocator, *sexp.first()).hex());

    assert_eq!(tree_hash, expected_hash);
}

#[test]
fn test_include_strict_fail() {
    let result = do_basic_run(&vec![
        "run".to_string(),
        "(mod () (include *strict*) (defun-inline foo (X) (+ X1 1)) (foo 3))".to_string(),
    ])
    .trim()
    .to_string();

    assert_eq!(result.find("Unknown variable reference X1").is_some(), true);
}

#[test]
fn test_include_strict_modern_fail() {
    let result =
        do_basic_run(&vec![
            "run".to_string(),
            "(mod () (include *strict*) (include *standard-cl-21*) (defun-inline foo (X) (+ X1 1)) (foo 3))".to_string()
        ])
        .trim().to_string();

    assert_eq!(result.find("Unknown variable reference X1").is_some(), true);
}

#[test]
fn test_include_strict_with_if_fail() {
    let result = do_basic_run(&vec![
        "run".to_string(),
        "(mod () (include *strict*) (defun-inline foo (X) (if X (+ X1 1) ())) (foo 3))".to_string(),
    ])
    .trim()
    .to_string();

    eprintln!("result {}", result);

    assert_eq!(result.find("Unknown variable reference X1").is_some(), true);
}

#[test]
fn test_include_strict_with_if_success() {
    let result = do_basic_run(&vec![
        "run".to_string(),
        "(mod () (include *strict*) (defun-inline foo (X) (if X (+ X 1) ())) (foo 3))".to_string(),
    ])
    .trim()
    .to_string();

    assert_eq!(result.find("Unknown variable reference X").is_none(), true);
}

#[test]
fn test_include_strict_with_list_fail() {
    let result = do_basic_run(&vec![
        "run".to_string(),
        "(mod (Y) (include *strict*) (defun-inline foo (X) (list X X Y)) (foo Y))".to_string(),
    ])
    .trim()
    .to_string();

    assert_eq!(result.find("Unknown variable reference Y").is_none(), true);
}

#[test]
fn test_assert_with_strict_succeed() {
    let result = do_basic_run(&vec![
        "run".to_string(),
        "-i".to_string(),
        "resources/tests".to_string(),
        "(mod (Y) (include *strict*) (include assert.clib) (defun-inline foo (X Y) (list X X Y)) (assert (foo 3 Y)))".to_string(),
    ])
        .trim()
        .to_string();

    eprintln!("result {}", result);
    assert_eq!(result.find(":").is_none(), true);
}
