open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Types
open Expr

let is_osx = Conf.make_bool "osx" false "Set this flag to run on osx";;

let t name program expected = name>::test_run program name expected;;

let ta name program expected = name>::test_run_anf program name expected;;

let te name program expected_err = name>::test_err program name expected_err;;

let tvg name program expected = name>::test_run_valgrind program name expected;;

let tanf name program expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

let tests =
[
  t "forty" "let x = 40 in x" "40";
  t "fals" "let x = false in x" "false";
  t "tru" "let x = true in x" "true";
  t "true1" "if true : 5 else: 10" "5";
  t "false1" "if false : 5 else: 10" "10";
  t "print1" "print(5 - 10)" "-5\n-5";
  t "comp_1" "if (5 > 7): true else: false" "false";
  t "comp_2" "if (5 < 7): true else: false" "true";
  t "comp_3" "if (5 == 7): true else: false" "false";
  t "comp_4" "if (5 == 5): true else: false" "true";

  t "m1" "5 - 5" "0";
  t "m2" "5 + 5" "10";
  t "m3" "5 * 5" "25";
  t "m4" "5 - 0" "5";
  t "m5" "5 + 0" "5";
  t "m6" "5 * 0" "0";
  t "m7" "let x = 5 in x" "5";
  t "m8" "let x = 5, y = 6 in x + y" "11";
  t "m9" "let x = 5 + 6 in x" "11";
  t "m10" "let x = let y = 5 + 6 in y in x - 6" "5";
  t "m11" "let x = 5 in let y = 5 + x in y" "10";
  t "m12" "let x = 5, y = 6 in let z = x + y in z" "11";
  t "m13" "let x = 5, y = 6 in let z = let a = x + y in a in z" "11";
  t "m14" "let x = 5 in 5 * x" "25";
  t "m15" "let x = 5, y = 6 in x * y" "30";
  t "m16" "let x = 5, y = 6 in let z = let a = x * y in a in z" "30";

  t "f1" "def sq(x): (x*x) def ten(): 10 sq(ten())" "100";
  t "f2" "def f(x,y): (x-y) f(4,1)" "3";
  t "f3" "def f(x,y,z): (x*y+z)
          def g(x,y): (x+y)
          def h(x,y): (2*x+y)
          f(g(3,4),g(2,2),h(5,9))" "47";
  t "f4" "def f(x,y,z,t): (x*y+z*t)
          def g(x,y): (x+y)
          def h(x,y): (2*x+y)
          def j(x): (x*x)
          j(f(g(4,4),h(2,2),g(5,5),h(3,3)))" "272484";
  t "f5" "def f(x): (if x==1: x else: 0) f(4)" "0";
  t "f6" "def f(x): (if x==1: x else: 1) f(1)" "1";
  t "f8" "def f(x): (if x==0: 1 else: (x * f(x - 1))) f(6)" "720";
  t "f9" "def f(x): (if x==0: 0 else: (x + f(x - 1))) f(24)" "300";
  t "f10" "def f(): 5 f()" "5";

  t "f_tail_1" "def f(x, a): (if x==1: a else: f(x - 1, a * x)) f(6, 1)" "720";
  t "f_tail_2" "def f(x, a): (if x==0: a else: f(x - 1, a + x)) f(99, 0)" "4950";
  t "f_tail_3" "def f(x, a): (if x==1: a else: g(x - 1, a * x))
                def g(x, a): (if x==1: a+1 else: f(x - 1, a + x)) f(16, 1)" "20643839";

  t "tup_1" "let x = (3, 4, 5, 6) in x[0]" "3";
  t "tup_2" "let x = (3, 4, 5, 6) in x[1]" "4";
  t "tup_3" "let x = (3, 4, 5, 6) in x[2]" "5";
  t "tup_4" "let x = (3, 4, 5, 6) in x[3]" "6";
  t "tup_5" "let x = (1, 2, 3, 4, 5, 6) in x[0]" "1";
  t "tup_6" "let x = (1, 2, 3, 4, 5, 6) in x[2]" "3";
  t "tup_7" "let x = (1, 2, 3, 4, 5, 6) in x[4]" "5";
  t "tup_8" "let x = (1, 2, 3, 4, 5, 6) in x[2+2]" "5";
  t "tup_9" "let x = (1, 2, 3, 4, 5, 6) in x[0+1]+x[1+2]+x[2+3]" "12";
  t "tup_10" "let x = (1, 2, 3, 4, 5, 6) in x[x[x[x[x[x[0]]]]]]" "6";
  t "tup_11" "let x = (0, false, 1, true) in x" "(0, false, 1, true)";
  t "tup_12" "let x = ((0, false), (1, true), (2, (true, false))) in x"
             "((0, false), (1, true), (2, (true, false)))";
  t "tup_13" "let x = (0, (1, 2)) in x[1]" "(1, 2)";
  t "tup_14" "let x = (0, (1, 2)) in x[1][0]" "1";
  t "tup_15" "let x = (0, (1, (3, 4))) in x[1][1][1]" "4";
  t "tup_16" "let x = (0, (1, (3, 4))) in x[1][1][1] + x[1][1][0]" "7";

  te "comp_num_1" "if (5 == true): 5 else: 10" "1";
  te "comp_num_2" "if (5 < true): 5 else: 10" "1";
  te "comp_num_3" "if (5 > true): 5 else: 10" "1";
  te "arith_num_1" "5 + true" "2";
  te "arith_num_2" "5 - true" "2";
  te "arith_num_3" "5 * true" "2";
  te "logic_bool_1" "!(5)" "3";
  te "logic_bool_2" "5 && 5" "3";
  te "logic_bool_3" "5 || 5" "3";
  te "if_num" "if 5 : 5 else: 10" "4";
  te "ovf_1" "999999999 * 999999999" "5";
  te "ovf_2" "def f(x, a): (if x==1: a else: f(x - 1, a * x)) f(99, 1)" "5";

  te "e1" "let x = 5 in x + y" "The identifier y, used at <e1, 1:17-1:18>, is not in scope";
  te "e2" "def f(x,y): (x+y) g(1,2)" "The function name g, used at <e2, 1:18-1:24>, is not in scope";
  te "e3" "let x = 5 in let x = 5 in 4" "The identifier x, defined at <e3, 1:17-1:18>, shadows one defined at <e3, 1:4-1:5>";
  te "e4" "def f(x): (x)
           def f(x): (x)
           f(f(5))"
          "The function name f, redefined at <e4, 2:11-2:24>, duplicates one at <e4, 1:0-1:13>";
  te "e5" "let x = 1073741824 in x" "The number literal 1073741824, used at <e5, 1:8-1:18>, is not supported in this language";
  te "e6" "let x = -1073741825 in x" "The number literal -1073741825, used at <e6, 1:8-1:19>, is not supported in this language";
  te "e7" "def f(x): (x)
           f(5, 6)"
          "The function called at <e7, 2:11-2:18> expected an arity of 1, but received 2 arguments";
  te "e8" "def f(x, y): (x+y)
           f(5)"
          "The function called at <e8, 2:11-2:15> expected an arity of 2, but received 1 argument";
  te "e9" "def f(x, x): (x+1) f(5, 6)" "The identifier x, redefined at <e9, 1:9-1:10>, duplicates one at <e9, 1:6-1:7>";
  te "e10" "def f(): 5 f(x)" "The function called at <e10, 1:11-1:15> expected an arity of 0, but received 1 arguments";
 ]

let suite =
"suite">:::tests




let () =
  run_test_tt_main suite
;;

