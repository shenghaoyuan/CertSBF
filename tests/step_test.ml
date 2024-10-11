module Step_test : sig
  type num
  type myint
  type nat
  type 'a word
  type 'a bit0
  type num1
  type bpf_ireg
  type sbpfv
  type 'a stack_state_ext
  type bpf_state
  type bpf_instruction
  val step_test :
    myint list ->
      myint list ->
        myint list -> myint list -> myint -> myint -> myint -> myint -> myint -> bool
  val int_of_standard_int : int64 -> myint
  val int_list_of_standard_int_list : int64 list -> myint list
end = struct

type num = One | Bit0 of num | Bit1 of num;;

let rec plus_num
  x0 x1 = match x0, x1 with Bit1 m, Bit1 n -> Bit0 (plus_num (plus_num m n) One)
    | Bit1 m, Bit0 n -> Bit1 (plus_num m n)
    | Bit1 m, One -> Bit0 (plus_num m One)
    | Bit0 m, Bit1 n -> Bit1 (plus_num m n)
    | Bit0 m, Bit0 n -> Bit0 (plus_num m n)
    | Bit0 m, One -> Bit1 m
    | One, Bit1 n -> Bit0 (plus_num n One)
    | One, Bit0 n -> Bit1 n
    | One, One -> Bit0 One;;

let rec times_num
  m n = match m, n with
    Bit1 m, Bit1 n -> Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
    | Bit1 m, Bit0 n -> Bit0 (times_num (Bit1 m) n)
    | Bit0 m, Bit1 n -> Bit0 (times_num m (Bit1 n))
    | Bit0 m, Bit0 n -> Bit0 (Bit0 (times_num m n))
    | One, n -> n
    | m, One -> m;;

type myint = Zero_int | Pos of num | Neg of num;;

let rec times_inta k l = match k, l with Neg m, Neg n -> Pos (times_num m n)
                     | Neg m, Pos n -> Neg (times_num m n)
                     | Pos m, Neg n -> Neg (times_num m n)
                     | Pos m, Pos n -> Pos (times_num m n)
                     | Zero_int, l -> Zero_int
                     | k, Zero_int -> Zero_int;;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a dvd = {times_dvd : 'a times};;

let times_int = ({times = times_inta} : myint times);;

let dvd_int = ({times_dvd = times_int} : myint dvd);;

let one_inta : myint = Pos One;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : myint one);;

let rec uminus_inta = function Neg m -> Pos m
                      | Pos m -> Neg m
                      | Zero_int -> Zero_int;;

let rec bitM = function One -> One
               | Bit0 n -> Bit1 (bitM n)
               | Bit1 n -> Bit1 (Bit0 n);;

let rec dup = function Neg n -> Neg (Bit0 n)
              | Pos n -> Pos (Bit0 n)
              | Zero_int -> Zero_int;;

let rec minus_inta k l = match k, l with Neg m, Neg n -> sub n m
                     | Neg m, Pos n -> Neg (plus_num m n)
                     | Pos m, Neg n -> Pos (plus_num m n)
                     | Pos m, Pos n -> sub m n
                     | Zero_int, l -> uminus_inta l
                     | k, Zero_int -> k
and sub
  x0 x1 = match x0, x1 with
    Bit0 m, Bit1 n -> minus_inta (dup (sub m n)) one_inta
    | Bit1 m, Bit0 n -> plus_inta (dup (sub m n)) one_inta
    | Bit1 m, Bit1 n -> dup (sub m n)
    | Bit0 m, Bit0 n -> dup (sub m n)
    | One, Bit1 n -> Neg (Bit0 n)
    | One, Bit0 n -> Neg (bitM n)
    | Bit1 m, One -> Pos (Bit0 m)
    | Bit0 m, One -> Pos (bitM m)
    | One, One -> Zero_int
and plus_inta k l = match k, l with Neg m, Neg n -> Neg (plus_num m n)
                | Neg m, Pos n -> sub n m
                | Pos m, Neg n -> sub m n
                | Pos m, Pos n -> Pos (plus_num m n)
                | Zero_int, l -> l
                | k, Zero_int -> k;;

type 'a uminus = {uminus : 'a -> 'a};;
let uminus _A = _A.uminus;;

type 'a minus = {minus : 'a -> 'a -> 'a};;
let minus _A = _A.minus;;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
    minus_cancel_ab_semigroup_add : 'a minus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add;
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};;

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add;
    semiring_0_semiring_0_cancel : 'a semiring_0};;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add;
    minus_group_add : 'a minus; monoid_add_group_add : 'a monoid_add;
    uminus_group_add : 'a uminus};;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add;
    group_add_ab_group_add : 'a group_add};;

type 'a ring =
  {ab_group_add_ring : 'a ab_group_add;
    semiring_0_cancel_ring : 'a semiring_0_cancel};;

let plus_int = ({plus = plus_inta} : myint plus);;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : myint semigroup_add);;

let cancel_semigroup_add_int =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_int} :
    myint cancel_semigroup_add);;

let ab_semigroup_add_int =
  ({semigroup_add_ab_semigroup_add = semigroup_add_int} :
    myint ab_semigroup_add);;

let minus_int = ({minus = minus_inta} : myint minus);;

let cancel_ab_semigroup_add_int =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int;
     minus_cancel_ab_semigroup_add = minus_int}
    : myint cancel_ab_semigroup_add);;

let zero_int = ({zero = Zero_int} : myint zero);;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    myint monoid_add);;

let comm_monoid_add_int =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int;
     monoid_add_comm_monoid_add = monoid_add_int}
    : myint comm_monoid_add);;

let cancel_comm_monoid_add_int =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_int;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
    : myint cancel_comm_monoid_add);;

let mult_zero_int =
  ({times_mult_zero = times_int; zero_mult_zero = zero_int} : myint mult_zero);;

let semigroup_mult_int =
  ({times_semigroup_mult = times_int} : myint semigroup_mult);;

let semiring_int =
  ({ab_semigroup_add_semiring = ab_semigroup_add_int;
     semigroup_mult_semiring = semigroup_mult_int}
    : myint semiring);;

let semiring_0_int =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_int;
     mult_zero_semiring_0 = mult_zero_int; semiring_semiring_0 = semiring_int}
    : myint semiring_0);;

let semiring_0_cancel_int =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int;
     semiring_0_semiring_0_cancel = semiring_0_int}
    : myint semiring_0_cancel);;

let uminus_int = ({uminus = uminus_inta} : myint uminus);;

let group_add_int =
  ({cancel_semigroup_add_group_add = cancel_semigroup_add_int;
     minus_group_add = minus_int; monoid_add_group_add = monoid_add_int;
     uminus_group_add = uminus_int}
    : myint group_add);;

let ab_group_add_int =
  ({cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int;
     group_add_ab_group_add = group_add_int}
    : myint ab_group_add);;

let ring_int =
  ({ab_group_add_ring = ab_group_add_int;
     semiring_0_cancel_ring = semiring_0_cancel_int}
    : myint ring);;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

let numeral_int =
  ({one_numeral = one_int; semigroup_add_numeral = semigroup_add_int} :
    myint numeral);;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let power_int = ({one_power = one_int; times_power = times_int} : myint power);;

let rec less_eq_num x0 n = match x0, n with Bit1 m, Bit0 n -> less_num m n
                      | Bit1 m, Bit1 n -> less_eq_num m n
                      | Bit0 m, Bit1 n -> less_eq_num m n
                      | Bit0 m, Bit0 n -> less_eq_num m n
                      | Bit1 m, One -> false
                      | Bit0 m, One -> false
                      | One, n -> true
and less_num m x1 = match m, x1 with Bit1 m, Bit0 n -> less_num m n
               | Bit1 m, Bit1 n -> less_num m n
               | Bit0 m, Bit1 n -> less_eq_num m n
               | Bit0 m, Bit0 n -> less_num m n
               | One, Bit1 n -> true
               | One, Bit0 n -> true
               | m, One -> false;;

let rec less_eq_int x0 x1 = match x0, x1 with Neg k, Neg l -> less_eq_num l k
                      | Neg k, Pos l -> true
                      | Neg k, Zero_int -> true
                      | Pos k, Neg l -> false
                      | Pos k, Pos l -> less_eq_num k l
                      | Pos k, Zero_int -> false
                      | Zero_int, Neg l -> false
                      | Zero_int, Pos l -> true
                      | Zero_int, Zero_int -> true;;

let rec less_int x0 x1 = match x0, x1 with Neg k, Neg l -> less_num l k
                   | Neg k, Pos l -> true
                   | Neg k, Zero_int -> true
                   | Pos k, Neg l -> false
                   | Pos k, Pos l -> less_num k l
                   | Pos k, Zero_int -> false
                   | Zero_int, Neg l -> false
                   | Zero_int, Pos l -> true
                   | Zero_int, Zero_int -> false;;

let rec abs_int i = (if less_int i Zero_int then uminus_inta i else i);;

let rec divmod_step_int
  l qr =
    (let (q, r) = qr in
      (if less_eq_int (abs_int l) (abs_int r)
        then (plus_inta (times_inta (Pos (Bit0 One)) q) one_inta,
               minus_inta r l)
        else (times_inta (Pos (Bit0 One)) q, r)));;

let rec divmod_int
  m x1 = match m, x1 with
    Bit1 m, Bit1 n ->
      (if less_num m n then (Zero_int, Pos (Bit1 m))
        else divmod_step_int (Pos (Bit1 n))
               (divmod_int (Bit1 m) (Bit0 (Bit1 n))))
    | Bit0 m, Bit1 n ->
        (if less_eq_num m n then (Zero_int, Pos (Bit0 m))
          else divmod_step_int (Pos (Bit1 n))
                 (divmod_int (Bit0 m) (Bit0 (Bit1 n))))
    | Bit1 m, Bit0 n ->
        (let (q, r) = divmod_int m n in
          (q, plus_inta (times_inta (Pos (Bit0 One)) r) one_inta))
    | Bit0 m, Bit0 n ->
        (let (q, r) = divmod_int m n in (q, times_inta (Pos (Bit0 One)) r))
    | One, Bit1 n -> (Zero_int, Pos One)
    | One, Bit0 n -> (Zero_int, Pos One)
    | m, One -> (Pos m, Zero_int);;

let rec fst (x1, x2) = x1;;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

let rec of_bool _A = function true -> one _A.one_zero_neq_one
                     | false -> zero _A.zero_zero_neq_one;;

let rec equal_num x0 x1 = match x0, x1 with Bit0 x2, Bit1 x3 -> false
                    | Bit1 x3, Bit0 x2 -> false
                    | One, Bit1 x3 -> false
                    | Bit1 x3, One -> false
                    | One, Bit0 x2 -> false
                    | Bit0 x2, One -> false
                    | Bit1 x3, Bit1 y3 -> equal_num x3 y3
                    | Bit0 x2, Bit0 y2 -> equal_num x2 y2
                    | One, One -> true;;

let rec equal_int x0 x1 = match x0, x1 with Neg k, Neg l -> equal_num k l
                    | Neg k, Pos l -> false
                    | Neg k, Zero_int -> false
                    | Pos k, Neg l -> false
                    | Pos k, Pos l -> equal_num k l
                    | Pos k, Zero_int -> false
                    | Zero_int, Neg l -> false
                    | Zero_int, Pos l -> false
                    | Zero_int, Zero_int -> true;;

let zero_neq_one_int =
  ({one_zero_neq_one = one_int; zero_zero_neq_one = zero_int} :
    myint zero_neq_one);;

let rec adjust_div
  (q, r) = plus_inta q (of_bool zero_neq_one_int (not (equal_int r Zero_int)));;

let rec divide_inta
  k ka = match k, ka with Neg m, Neg n -> fst (divmod_int m n)
    | Pos m, Neg n -> uminus_inta (adjust_div (divmod_int m n))
    | Neg m, Pos n -> uminus_inta (adjust_div (divmod_int m n))
    | Pos m, Pos n -> fst (divmod_int m n)
    | k, Neg One -> uminus_inta k
    | k, Pos One -> k
    | Zero_int, k -> Zero_int
    | k, Zero_int -> Zero_int;;

type 'a divide = {divide : 'a -> 'a -> 'a};;
let divide _A = _A.divide;;

let divide_int = ({divide = divide_inta} : myint divide);;

let rec snd (x1, x2) = x2;;

let rec adjust_mod
  l r = (if equal_int r Zero_int then Zero_int else minus_inta (Pos l) r);;

let rec modulo_inta
  k ka = match k, ka with Neg m, Neg n -> uminus_inta (snd (divmod_int m n))
    | Pos m, Neg n -> uminus_inta (adjust_mod n (snd (divmod_int m n)))
    | Neg m, Pos n -> adjust_mod n (snd (divmod_int m n))
    | Pos m, Pos n -> snd (divmod_int m n)
    | k, Neg One -> Zero_int
    | k, Pos One -> Zero_int
    | Zero_int, k -> Zero_int
    | k, Zero_int -> k;;

type 'a modulo =
  {divide_modulo : 'a divide; dvd_modulo : 'a dvd; modulo : 'a -> 'a -> 'a};;
let modulo _A = _A.modulo;;

let modulo_int =
  ({divide_modulo = divide_int; dvd_modulo = dvd_int; modulo = modulo_inta} :
    myint modulo);;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel;
    semiring_1_semiring_1_cancel : 'a semiring_1};;

type 'a neg_numeral =
  {group_add_neg_numeral : 'a group_add; numeral_neg_numeral : 'a numeral};;

type 'a ring_1 =
  {neg_numeral_ring_1 : 'a neg_numeral; ring_ring_1 : 'a ring;
    semiring_1_cancel_ring_1 : 'a semiring_1_cancel};;

let monoid_mult_int =
  ({semigroup_mult_monoid_mult = semigroup_mult_int;
     power_monoid_mult = power_int}
    : myint monoid_mult);;

let semiring_numeral_int =
  ({monoid_mult_semiring_numeral = monoid_mult_int;
     numeral_semiring_numeral = numeral_int;
     semiring_semiring_numeral = semiring_int}
    : myint semiring_numeral);;

let semiring_1_int =
  ({semiring_numeral_semiring_1 = semiring_numeral_int;
     semiring_0_semiring_1 = semiring_0_int;
     zero_neq_one_semiring_1 = zero_neq_one_int}
    : myint semiring_1);;

let semiring_1_cancel_int =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int;
     semiring_1_semiring_1_cancel = semiring_1_int}
    : myint semiring_1_cancel);;

let neg_numeral_int =
  ({group_add_neg_numeral = group_add_int; numeral_neg_numeral = numeral_int} :
    myint neg_numeral);;

let ring_1_int =
  ({neg_numeral_ring_1 = neg_numeral_int; ring_ring_1 = ring_int;
     semiring_1_cancel_ring_1 = semiring_1_cancel_int}
    : myint ring_1);;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult;
    semiring_comm_semiring : 'a semiring};;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring;
    semiring_0_comm_semiring_0 : 'a semiring_0};;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0;
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};;

type 'a comm_ring =
  {comm_semiring_0_cancel_comm_ring : 'a comm_semiring_0_cancel;
    ring_comm_ring : 'a ring};;

let ab_semigroup_mult_int =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
    myint ab_semigroup_mult);;

let comm_semiring_int =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int;
     semiring_comm_semiring = semiring_int}
    : myint comm_semiring);;

let comm_semiring_0_int =
  ({comm_semiring_comm_semiring_0 = comm_semiring_int;
     semiring_0_comm_semiring_0 = semiring_0_int}
    : myint comm_semiring_0);;

let comm_semiring_0_cancel_int =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
    : myint comm_semiring_0_cancel);;

let comm_ring_int =
  ({comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_int;
     ring_comm_ring = ring_int}
    : myint comm_ring);;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult;
    monoid_mult_comm_monoid_mult : 'a monoid_mult;
    dvd_comm_monoid_mult : 'a dvd};;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult;
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0;
    semiring_1_comm_semiring_1 : 'a semiring_1};;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel;
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1;
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};;

type 'a comm_ring_1 =
  {comm_ring_comm_ring_1 : 'a comm_ring;
    comm_semiring_1_cancel_comm_ring_1 : 'a comm_semiring_1_cancel;
    ring_1_comm_ring_1 : 'a ring_1};;

let comm_monoid_mult_int =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int;
     monoid_mult_comm_monoid_mult = monoid_mult_int;
     dvd_comm_monoid_mult = dvd_int}
    : myint comm_monoid_mult);;

let comm_semiring_1_int =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_int;
     semiring_1_comm_semiring_1 = semiring_1_int}
    : myint comm_semiring_1);;

let comm_semiring_1_cancel_int =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
    : myint comm_semiring_1_cancel);;

let comm_ring_1_int =
  ({comm_ring_comm_ring_1 = comm_ring_int;
     comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_int;
     ring_1_comm_ring_1 = ring_1_int}
    : myint comm_ring_1);;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel;
    modulo_semiring_modulo : 'a modulo};;

type 'a semiring_parity =
  {semiring_modulo_semiring_parity : 'a semiring_modulo};;

type 'a ring_parity =
  {semiring_parity_ring_parity : 'a semiring_parity;
    comm_ring_1_ring_parity : 'a comm_ring_1};;

let semiring_modulo_int =
  ({comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_int;
     modulo_semiring_modulo = modulo_int}
    : myint semiring_modulo);;

let semiring_parity_int =
  ({semiring_modulo_semiring_parity = semiring_modulo_int} :
    myint semiring_parity);;

let ring_parity_int =
  ({semiring_parity_ring_parity = semiring_parity_int;
     comm_ring_1_ring_parity = comm_ring_1_int}
    : myint ring_parity);;

type 'a divide_trivial =
  {one_divide_trivial : 'a one; zero_divide_trivial : 'a zero;
    divide_divide_trivial : 'a divide};;

let divide_trivial_int =
  ({one_divide_trivial = one_int; zero_divide_trivial = zero_int;
     divide_divide_trivial = divide_int}
    : myint divide_trivial);;

type nat = Zero_nat | Suc of nat;;

let rec inc = function One -> Bit0 One
              | Bit0 x -> Bit1 x
              | Bit1 x -> Bit0 (inc x);;

let rec bit_int
  x0 n = match x0, n with Neg (Bit1 m), Suc n -> bit_int (Neg (inc m)) n
    | Neg (Bit0 m), Suc n -> bit_int (Neg m) n
    | Pos (Bit1 m), Suc n -> bit_int (Pos m) n
    | Pos (Bit0 m), Suc n -> bit_int (Pos m) n
    | Pos One, Suc n -> false
    | Neg (Bit1 m), Zero_nat -> true
    | Neg (Bit0 m), Zero_nat -> false
    | Pos (Bit1 m), Zero_nat -> true
    | Pos (Bit0 m), Zero_nat -> false
    | Pos One, Zero_nat -> true
    | Neg One, n -> true
    | Zero_int, n -> false;;

type 'a semiring_modulo_trivial =
  {divide_trivial_semiring_modulo_trivial : 'a divide_trivial;
    semiring_modulo_semiring_modulo_trivial : 'a semiring_modulo};;

type 'a semiring_bits =
  {semiring_parity_semiring_bits : 'a semiring_parity;
    semiring_modulo_trivial_semiring_bits : 'a semiring_modulo_trivial;
    bit : 'a -> nat -> bool};;
let bit _A = _A.bit;;

let semiring_modulo_trivial_int =
  ({divide_trivial_semiring_modulo_trivial = divide_trivial_int;
     semiring_modulo_semiring_modulo_trivial = semiring_modulo_int}
    : myint semiring_modulo_trivial);;

let semiring_bits_int =
  ({semiring_parity_semiring_bits = semiring_parity_int;
     semiring_modulo_trivial_semiring_bits = semiring_modulo_trivial_int;
     bit = bit_int}
    : myint semiring_bits);;

let rec push_bit_int
  x0 i = match x0, i with Suc n, i -> push_bit_int n (dup i)
    | Zero_nat, i -> i;;

let rec or_num x0 x1 = match x0, x1 with One, One -> One
                 | One, Bit0 n -> Bit1 n
                 | One, Bit1 n -> Bit1 n
                 | Bit0 m, One -> Bit1 m
                 | Bit0 m, Bit0 n -> Bit0 (or_num m n)
                 | Bit0 m, Bit1 n -> Bit1 (or_num m n)
                 | Bit1 m, One -> Bit1 m
                 | Bit1 m, Bit0 n -> Bit1 (or_num m n)
                 | Bit1 m, Bit1 n -> Bit1 (or_num m n);;

let rec numeral _A
  = function
    Bit1 n ->
      (let m = numeral _A n in
        plus _A.semigroup_add_numeral.plus_semigroup_add
          (plus _A.semigroup_add_numeral.plus_semigroup_add m m)
          (one _A.one_numeral))
    | Bit0 n ->
        (let m = numeral _A n in
          plus _A.semigroup_add_numeral.plus_semigroup_add m m)
    | One -> one _A.one_numeral;;

let rec suba _A
  k l = minus _A.group_add_neg_numeral.minus_group_add
          (numeral _A.numeral_neg_numeral k)
          (numeral _A.numeral_neg_numeral l);;

let rec not_int = function Neg n -> suba neg_numeral_int n One
                  | Pos n -> Neg (inc n)
                  | Zero_int -> uminus_inta one_inta;;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec and_not_num
  x0 x1 = match x0, x1 with One, One -> None
    | One, Bit0 n -> Some One
    | One, Bit1 n -> None
    | Bit0 m, One -> Some (Bit0 m)
    | Bit0 m, Bit0 n -> map_option (fun a -> Bit0 a) (and_not_num m n)
    | Bit0 m, Bit1 n -> map_option (fun a -> Bit0 a) (and_not_num m n)
    | Bit1 m, One -> Some (Bit0 m)
    | Bit1 m, Bit0 n ->
        (match and_not_num m n with None -> Some One
          | Some na -> Some (Bit1 na))
    | Bit1 m, Bit1 n -> map_option (fun a -> Bit0 a) (and_not_num m n);;

let rec or_not_num_neg x0 x1 = match x0, x1 with One, One -> One
                         | One, Bit0 m -> Bit1 m
                         | One, Bit1 m -> Bit1 m
                         | Bit0 n, One -> Bit0 One
                         | Bit0 n, Bit0 m -> bitM (or_not_num_neg n m)
                         | Bit0 n, Bit1 m -> Bit0 (or_not_num_neg n m)
                         | Bit1 n, One -> One
                         | Bit1 n, Bit0 m -> bitM (or_not_num_neg n m)
                         | Bit1 n, Bit1 m -> bitM (or_not_num_neg n m);;

let rec and_num
  x0 x1 = match x0, x1 with One, One -> Some One
    | One, Bit0 n -> None
    | One, Bit1 n -> Some One
    | Bit0 m, One -> None
    | Bit0 m, Bit0 n -> map_option (fun a -> Bit0 a) (and_num m n)
    | Bit0 m, Bit1 n -> map_option (fun a -> Bit0 a) (and_num m n)
    | Bit1 m, One -> Some One
    | Bit1 m, Bit0 n -> map_option (fun a -> Bit0 a) (and_num m n)
    | Bit1 m, Bit1 n ->
        (match and_num m n with None -> Some One | Some na -> Some (Bit1 na));;

let rec and_int
  i j = match i, j with
    Neg (Bit1 n), Pos m -> suba neg_numeral_int (or_not_num_neg (Bit0 n) m) One
    | Neg (Bit0 n), Pos m ->
        suba neg_numeral_int (or_not_num_neg (bitM n) m) One
    | Neg One, Pos m -> Pos m
    | Pos n, Neg (Bit1 m) ->
        suba neg_numeral_int (or_not_num_neg (Bit0 m) n) One
    | Pos n, Neg (Bit0 m) ->
        suba neg_numeral_int (or_not_num_neg (bitM m) n) One
    | Pos n, Neg One -> Pos n
    | Neg n, Neg m ->
        not_int
          (or_int (suba neg_numeral_int n One) (suba neg_numeral_int m One))
    | Pos n, Pos m ->
        (match and_num n m with None -> Zero_int | Some a -> Pos a)
    | i, Zero_int -> Zero_int
    | Zero_int, j -> Zero_int
and or_int
  i j = match i, j with
    Neg (Bit1 n), Pos m ->
      (match and_not_num (Bit0 n) m with None -> uminus_inta one_inta
        | Some na -> Neg (inc na))
    | Neg (Bit0 n), Pos m ->
        (match and_not_num (bitM n) m with None -> uminus_inta one_inta
          | Some na -> Neg (inc na))
    | Neg One, Pos m -> Neg One
    | Pos n, Neg (Bit1 m) ->
        (match and_not_num (Bit0 m) n with None -> uminus_inta one_inta
          | Some na -> Neg (inc na))
    | Pos n, Neg (Bit0 m) ->
        (match and_not_num (bitM m) n with None -> uminus_inta one_inta
          | Some na -> Neg (inc na))
    | Pos n, Neg One -> Neg One
    | Neg n, Neg m ->
        not_int
          (and_int (suba neg_numeral_int n One) (suba neg_numeral_int m One))
    | Pos n, Pos m -> Pos (or_num n m)
    | i, Zero_int -> i
    | Zero_int, j -> j;;

let rec unset_bit_int n k = and_int k (not_int (push_bit_int n one_inta));;

let rec power _A a x1 = match a, x1 with a, Zero_nat -> one _A.one_power
                   | a, Suc n -> times _A.times_power a (power _A a n);;

let rec take_bit_int n k = modulo_inta k (power power_int (Pos (Bit0 One)) n);;

let rec xor_num
  x0 x1 = match x0, x1 with One, One -> None
    | One, Bit0 n -> Some (Bit1 n)
    | One, Bit1 n -> Some (Bit0 n)
    | Bit0 m, One -> Some (Bit1 m)
    | Bit0 m, Bit0 n -> map_option (fun a -> Bit0 a) (xor_num m n)
    | Bit0 m, Bit1 n ->
        Some (match xor_num m n with None -> One | Some a -> Bit1 a)
    | Bit1 m, One -> Some (Bit0 m)
    | Bit1 m, Bit0 n ->
        Some (match xor_num m n with None -> One | Some a -> Bit1 a)
    | Bit1 m, Bit1 n -> map_option (fun a -> Bit0 a) (xor_num m n);;

let rec xor_int
  i j = match i, j with
    Pos n, Neg m -> not_int (xor_int (Pos n) (suba neg_numeral_int m One))
    | Neg n, Pos m -> not_int (xor_int (suba neg_numeral_int n One) (Pos m))
    | Neg n, Neg m ->
        xor_int (suba neg_numeral_int n One) (suba neg_numeral_int m One)
    | Pos n, Pos m ->
        (match xor_num n m with None -> Zero_int | Some a -> Pos a)
    | i, Zero_int -> i
    | Zero_int, j -> j;;

let rec flip_bit_int n k = xor_int k (push_bit_int n one_inta);;

let rec drop_bit_int
  x0 i = match x0, i with Suc n, Neg (Bit1 m) -> drop_bit_int n (Neg (inc m))
    | Suc n, Neg (Bit0 m) -> drop_bit_int n (Neg m)
    | Suc n, Neg One -> uminus_inta one_inta
    | Suc n, Pos (Bit1 m) -> drop_bit_int n (Pos m)
    | Suc n, Pos (Bit0 m) -> drop_bit_int n (Pos m)
    | Suc n, Pos One -> Zero_int
    | Suc n, Zero_int -> Zero_int
    | Zero_nat, i -> i;;

let rec set_bit_int n k = or_int k (push_bit_int n one_inta);;

let rec mask_int n = minus_inta (power power_int (Pos (Bit0 One)) n) one_inta;;

type 'a semiring_bit_operations =
  {semiring_bits_semiring_bit_operations : 'a semiring_bits;
    anda : 'a -> 'a -> 'a; ora : 'a -> 'a -> 'a; xor : 'a -> 'a -> 'a;
    mask : nat -> 'a; set_bit : nat -> 'a -> 'a; unset_bit : nat -> 'a -> 'a;
    flip_bit : nat -> 'a -> 'a; push_bit : nat -> 'a -> 'a;
    drop_bit : nat -> 'a -> 'a; take_bit : nat -> 'a -> 'a};;
let anda _A = _A.anda;;
let ora _A = _A.ora;;
let xor _A = _A.xor;;
let mask _A = _A.mask;;
let set_bit _A = _A.set_bit;;
let unset_bit _A = _A.unset_bit;;
let flip_bit _A = _A.flip_bit;;
let push_bit _A = _A.push_bit;;
let drop_bit _A = _A.drop_bit;;
let take_bit _A = _A.take_bit;;

type 'a ring_bit_operations =
  {semiring_bit_operations_ring_bit_operations : 'a semiring_bit_operations;
    ring_parity_ring_bit_operations : 'a ring_parity; nota : 'a -> 'a};;
let nota _A = _A.nota;;

let semiring_bit_operations_int =
  ({semiring_bits_semiring_bit_operations = semiring_bits_int; anda = and_int;
     ora = or_int; xor = xor_int; mask = mask_int; set_bit = set_bit_int;
     unset_bit = unset_bit_int; flip_bit = flip_bit_int;
     push_bit = push_bit_int; drop_bit = drop_bit_int; take_bit = take_bit_int}
    : myint semiring_bit_operations);;

let ring_bit_operations_int =
  ({semiring_bit_operations_ring_bit_operations = semiring_bit_operations_int;
     ring_parity_ring_bit_operations = ring_parity_int; nota = not_int}
    : myint ring_bit_operations);;

type 'a itself = Type;;

type 'a len0 = {len_of : 'a itself -> nat};;
let len_of _A = _A.len_of;;

type 'a len = {len0_len : 'a len0};;

type 'a word = Word of myint;;

let rec one_worda _A = Word one_inta;;

let rec one_word _A = ({one = one_worda _A} : 'a word one);;

let rec the_int _A (Word x) = x;;

let rec of_int _A k = Word (take_bit_int (len_of _A.len0_len Type) k);;

let rec times_worda _A
  a b = of_int _A (times_inta (the_int _A a) (the_int _A b));;

let rec times_word _A = ({times = times_worda _A} : 'a word times);;

let rec power_word _A =
  ({one_power = (one_word _A); times_power = (times_word _A)} : 'a word power);;

let rec plus_nat x0 n = match x0, n with Suc m, n -> plus_nat m (Suc n)
                   | Zero_nat, n -> n;;

let rec times_nat x0 n = match x0, n with Zero_nat, n -> Zero_nat
                    | Suc m, n -> plus_nat n (times_nat m n);;

let one_nat : nat = Suc Zero_nat;;

let rec nat_of_num
  = function Bit1 n -> (let m = nat_of_num n in Suc (plus_nat m m))
    | Bit0 n -> (let m = nat_of_num n in plus_nat m m)
    | One -> one_nat;;

type 'a finite = unit;;

type 'a bit0 = Abs_bit0 of myint;;

let rec len_of_bit0 _A uu = times_nat (nat_of_num (Bit0 One)) (len_of _A Type);;

let rec len0_bit0 _A = ({len_of = len_of_bit0 _A} : 'a bit0 len0);;

let rec len_bit0 _A = ({len0_len = (len0_bit0 _A.len0_len)} : 'a bit0 len);;

type num1 = One_num1;;

let rec len_of_num1 uu = one_nat;;

let len0_num1 = ({len_of = len_of_num1} : num1 len0);;

let len_num1 = ({len0_len = len0_num1} : num1 len);;

type 'a signed = EMPTY__;;

let rec len_of_signed _A x = len_of _A Type;;

let rec len0_signed _A = ({len_of = len_of_signed _A} : 'a signed len0);;

let rec len_signed _A =
  ({len0_len = (len0_signed _A.len0_len)} : 'a signed len);;

type bpf_ireg = BR0 | BR1 | BR2 | BR3 | BR4 | BR5 | BR6 | BR7 | BR8 | BR9 |
  BR10;;

let rec equal_bpf_irega x0 x1 = match x0, x1 with BR9, BR10 -> false
                          | BR10, BR9 -> false
                          | BR8, BR10 -> false
                          | BR10, BR8 -> false
                          | BR8, BR9 -> false
                          | BR9, BR8 -> false
                          | BR7, BR10 -> false
                          | BR10, BR7 -> false
                          | BR7, BR9 -> false
                          | BR9, BR7 -> false
                          | BR7, BR8 -> false
                          | BR8, BR7 -> false
                          | BR6, BR10 -> false
                          | BR10, BR6 -> false
                          | BR6, BR9 -> false
                          | BR9, BR6 -> false
                          | BR6, BR8 -> false
                          | BR8, BR6 -> false
                          | BR6, BR7 -> false
                          | BR7, BR6 -> false
                          | BR5, BR10 -> false
                          | BR10, BR5 -> false
                          | BR5, BR9 -> false
                          | BR9, BR5 -> false
                          | BR5, BR8 -> false
                          | BR8, BR5 -> false
                          | BR5, BR7 -> false
                          | BR7, BR5 -> false
                          | BR5, BR6 -> false
                          | BR6, BR5 -> false
                          | BR4, BR10 -> false
                          | BR10, BR4 -> false
                          | BR4, BR9 -> false
                          | BR9, BR4 -> false
                          | BR4, BR8 -> false
                          | BR8, BR4 -> false
                          | BR4, BR7 -> false
                          | BR7, BR4 -> false
                          | BR4, BR6 -> false
                          | BR6, BR4 -> false
                          | BR4, BR5 -> false
                          | BR5, BR4 -> false
                          | BR3, BR10 -> false
                          | BR10, BR3 -> false
                          | BR3, BR9 -> false
                          | BR9, BR3 -> false
                          | BR3, BR8 -> false
                          | BR8, BR3 -> false
                          | BR3, BR7 -> false
                          | BR7, BR3 -> false
                          | BR3, BR6 -> false
                          | BR6, BR3 -> false
                          | BR3, BR5 -> false
                          | BR5, BR3 -> false
                          | BR3, BR4 -> false
                          | BR4, BR3 -> false
                          | BR2, BR10 -> false
                          | BR10, BR2 -> false
                          | BR2, BR9 -> false
                          | BR9, BR2 -> false
                          | BR2, BR8 -> false
                          | BR8, BR2 -> false
                          | BR2, BR7 -> false
                          | BR7, BR2 -> false
                          | BR2, BR6 -> false
                          | BR6, BR2 -> false
                          | BR2, BR5 -> false
                          | BR5, BR2 -> false
                          | BR2, BR4 -> false
                          | BR4, BR2 -> false
                          | BR2, BR3 -> false
                          | BR3, BR2 -> false
                          | BR1, BR10 -> false
                          | BR10, BR1 -> false
                          | BR1, BR9 -> false
                          | BR9, BR1 -> false
                          | BR1, BR8 -> false
                          | BR8, BR1 -> false
                          | BR1, BR7 -> false
                          | BR7, BR1 -> false
                          | BR1, BR6 -> false
                          | BR6, BR1 -> false
                          | BR1, BR5 -> false
                          | BR5, BR1 -> false
                          | BR1, BR4 -> false
                          | BR4, BR1 -> false
                          | BR1, BR3 -> false
                          | BR3, BR1 -> false
                          | BR1, BR2 -> false
                          | BR2, BR1 -> false
                          | BR0, BR10 -> false
                          | BR10, BR0 -> false
                          | BR0, BR9 -> false
                          | BR9, BR0 -> false
                          | BR0, BR8 -> false
                          | BR8, BR0 -> false
                          | BR0, BR7 -> false
                          | BR7, BR0 -> false
                          | BR0, BR6 -> false
                          | BR6, BR0 -> false
                          | BR0, BR5 -> false
                          | BR5, BR0 -> false
                          | BR0, BR4 -> false
                          | BR4, BR0 -> false
                          | BR0, BR3 -> false
                          | BR3, BR0 -> false
                          | BR0, BR2 -> false
                          | BR2, BR0 -> false
                          | BR0, BR1 -> false
                          | BR1, BR0 -> false
                          | BR10, BR10 -> true
                          | BR9, BR9 -> true
                          | BR8, BR8 -> true
                          | BR7, BR7 -> true
                          | BR6, BR6 -> true
                          | BR5, BR5 -> true
                          | BR4, BR4 -> true
                          | BR3, BR3 -> true
                          | BR2, BR2 -> true
                          | BR1, BR1 -> true
                          | BR0, BR0 -> true;;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_bpf_ireg = ({equal = equal_bpf_irega} : bpf_ireg equal);;

type vala = Vundef | Vbyte of num1 bit0 bit0 bit0 word |
  Vshort of num1 bit0 bit0 bit0 bit0 word |
  Vint of num1 bit0 bit0 bit0 bit0 bit0 word |
  Vlong of num1 bit0 bit0 bit0 bit0 bit0 bit0 word;;

type memory_chunk = M8 | M16 | M32 | M64;;

type sbpfv = V1 | V2;;

type binop = BPF_ADD | BPF_SUB | BPF_MUL | BPF_DIV | BPF_OR | BPF_AND | BPF_LSH
  | BPF_RSH | BPF_MOD | BPF_XOR | BPF_MOV | BPF_ARSH;;

type pqrop = BPF_LMUL | BPF_UDIV | BPF_UREM | BPF_SDIV | BPF_SREM;;

type pqrop2 = BPF_UHMUL | BPF_SHMUL;;

type snd_op = SOImm of num1 bit0 bit0 bit0 bit0 bit0 signed word |
  SOReg of bpf_ireg;;

type 'a option2 = NOK | OKS of 'a | OKN;;

type condition = Eq | Gt | Ge | Lt | Le | SEt | Ne | SGt | SGe | SLt | SLe;;

type 'a callFrame_ext =
  CallFrame_ext of
    num1 bit0 bit0 bit0 bit0 bit0 bit0 word list *
      num1 bit0 bit0 bit0 bit0 bit0 bit0 word *
      num1 bit0 bit0 bit0 bit0 bit0 bit0 word * 'a;;

type 'a stack_state_ext =
  Stack_state_ext of
    num1 bit0 bit0 bit0 bit0 bit0 bit0 word *
      num1 bit0 bit0 bit0 bit0 bit0 bit0 word * unit callFrame_ext list * 'a;;

type bpf_state =
  BPF_OK of
    num1 bit0 bit0 bit0 bit0 bit0 bit0 word *
      (bpf_ireg -> num1 bit0 bit0 bit0 bit0 bit0 bit0 word) *
      (num1 bit0 bit0 bit0 bit0 bit0 bit0 word ->
        num1 bit0 bit0 bit0 word option) *
      unit stack_state_ext * sbpfv *
      (num1 bit0 bit0 bit0 bit0 bit0 word ->
        num1 bit0 bit0 bit0 bit0 bit0 bit0 word option) *
      num1 bit0 bit0 bit0 bit0 bit0 bit0 word *
      num1 bit0 bit0 bit0 bit0 bit0 bit0 word
  | BPF_Success of num1 bit0 bit0 bit0 bit0 bit0 bit0 word | BPF_EFlag |
  BPF_Err;;

type bpf_instruction =
  BPF_LD_IMM of
    bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word *
      num1 bit0 bit0 bit0 bit0 bit0 signed word
  | BPF_LDX of
      memory_chunk * bpf_ireg * bpf_ireg * num1 bit0 bit0 bit0 bit0 signed word
  | BPF_ST of
      memory_chunk * bpf_ireg * snd_op * num1 bit0 bit0 bit0 bit0 signed word
  | BPF_ADD_STK of num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_ALU of binop * bpf_ireg * snd_op | BPF_NEG32_REG of bpf_ireg |
  BPF_LE of bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_BE of bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_ALU64 of binop * bpf_ireg * snd_op | BPF_NEG64_REG of bpf_ireg |
  BPF_HOR64_IMM of bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_PQR of pqrop * bpf_ireg * snd_op | BPF_PQR64 of pqrop * bpf_ireg * snd_op
  | BPF_PQR2 of pqrop2 * bpf_ireg * snd_op |
  BPF_JA of num1 bit0 bit0 bit0 bit0 signed word |
  BPF_JUMP of
    condition * bpf_ireg * snd_op * num1 bit0 bit0 bit0 bit0 signed word
  | BPF_CALL_REG of bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_CALL_IMM of bpf_ireg * num1 bit0 bit0 bit0 bit0 bit0 signed word |
  BPF_EXIT;;

let rec eq _A a b = equal _A a b;;

let rec nat = function Pos k -> nat_of_num k
              | Zero_int -> Zero_nat
              | Neg k -> Zero_nat;;

let rec nth x0 x1 = match x0, x1 with x :: xs, Suc n -> nth xs n
              | x :: xs, Zero_nat -> x;;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec plus_word _A a b = of_int _A (plus_inta (the_int _A a) (the_int _A b));;

let rec push_bit_word _A
  n w = times_worda _A w
          (power (power_word _A) (of_int _A (Pos (Bit0 One))) n);;

let rec or_word _A v w = Word (or_int (the_int _A v) (the_int _A w));;

let rec cast _B _A
  w = Word (take_bit_int (len_of _A.len0_len Type) (the_int _B w));;

let rec option_u64_of_u8_8
  v0 v1 v2 v3 v4 v5 v6 v7 =
    (match v0 with None -> None
      | Some n0 ->
        (match v1 with None -> None
          | Some n1 ->
            (match v2 with None -> None
              | Some n2 ->
                (match v3 with None -> None
                  | Some n3 ->
                    (match v4 with None -> None
                      | Some n4 ->
                        (match v5 with None -> None
                          | Some n5 ->
                            (match v6 with None -> None
                              | Some n6 ->
                                (match v7 with None -> None
                                  | Some n7 ->
                                    Some (or_word
   (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
   (push_bit_word
     (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
     (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One))))))
     (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
       (len_bit0
         (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
       n7))
   (or_word
     (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
     (push_bit_word
       (len_bit0
         (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
       (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))))
       (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         n6))
     (or_word
       (len_bit0
         (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
       (push_bit_word
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))
         (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
           n5))
       (or_word
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (push_bit_word
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
           (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
           (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
             (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             n4))
         (or_word
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
           (push_bit_word
             (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One)))))
             (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
               (len_bit0
                 (len_bit0
                   (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               n3))
           (or_word
             (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             (push_bit_word
               (len_bit0
                 (len_bit0
                   (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One)))))
               (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 n2))
             (or_word
               (len_bit0
                 (len_bit0
                   (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               (push_bit_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 (nat_of_num (Bit0 (Bit0 (Bit0 One))))
                 (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   n1))
               (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 n0))))))))))))))));;

let rec option_u64_of_u8_4
  v0 v1 v2 v3 =
    (match v0 with None -> None
      | Some n0 ->
        (match v1 with None -> None
          | Some n1 ->
            (match v2 with None -> None
              | Some n2 ->
                (match v3 with None -> None
                  | Some n3 ->
                    Some (or_word
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                           (push_bit_word
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One)))))
                             (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                               (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1))))))
                               n3))
                           (or_word
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             (push_bit_word
                               (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1))))))
                               (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One)))))
                               (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 len_num1))))))
                                 n2))
                             (or_word
                               (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1))))))
                               (push_bit_word
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 len_num1))))))
                                 (nat_of_num (Bit0 (Bit0 (Bit0 One))))
                                 (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                   n1))
                               (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 len_num1))))))
                                 n0))))))));;

let rec option_u64_of_u8_2
  v0 v1 =
    (match v0 with None -> None
      | Some n0 ->
        (match v1 with None -> None
          | Some n1 ->
            Some (or_word
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   (push_bit_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     (nat_of_num (Bit0 (Bit0 (Bit0 One))))
                     (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                       (len_bit0
                         (len_bit0
                           (len_bit0
                             (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                       n1))
                   (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     n0))));;

let rec option_u64_of_u8_1
  v0 = (match v0 with None -> None
         | Some v ->
           Some (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  v));;

let rec memory_chunk_value_of_u64
  mc v =
    (match mc
      with M8 ->
        Vbyte (cast (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                (len_bit0 (len_bit0 (len_bit0 len_num1))) v)
      | M16 ->
        Vshort
          (cast (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))) v)
      | M32 ->
        Vint (cast (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
               v)
      | M64 ->
        Vlong (cast (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                v));;

let rec option_val_of_u64
  mc v =
    (match v with None -> None
      | Some v1 -> Some (memory_chunk_value_of_u64 mc v1));;

let rec loadv
  mc m addr =
    option_val_of_u64 mc
      (match mc with M8 -> option_u64_of_u8_1 (m addr)
        | M16 ->
          option_u64_of_u8_2 (m addr)
            (m (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 addr
                 (one_worda
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))))
        | M32 ->
          option_u64_of_u8_4 (m addr)
            (m (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 addr
                 (one_worda
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))))
            (m (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 addr
                 (of_int
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   (Pos (Bit0 One)))))
            (m (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 addr
                 (of_int
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   (Pos (Bit1 One)))))
        | M64 ->
          option_u64_of_u8_8 (m addr)
            (m (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 addr
                 (one_worda
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))))
            (m (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 addr
                 (of_int
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   (Pos (Bit0 One)))))
            (m (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 addr
                 (of_int
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   (Pos (Bit1 One)))))
            (m (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 addr
                 (of_int
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   (Pos (Bit0 (Bit0 One))))))
            (m (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 addr
                 (of_int
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   (Pos (Bit1 (Bit0 One))))))
            (m (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 addr
                 (of_int
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   (Pos (Bit0 (Bit1 One))))))
            (m (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 addr
                 (of_int
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   (Pos (Bit1 (Bit1 One)))))));;

let rec equal_word _A v w = equal_int (the_int _A v) (the_int _A w);;

let rec drop_bit_word _A n w = Word (drop_bit_int n (the_int _A w));;

let rec and_word _A v w = Word (and_int (the_int _A v) (the_int _A w));;

let rec u8_list_of_u64
  i = [cast (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (and_word
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
           i (of_int
               (len_bit0
                 (len_bit0
                   (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 One)))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (drop_bit_word
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))) i)
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))))];;

let rec u8_list_of_u32
  i = [cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
         (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (and_word
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) i
           (of_int
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
             (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
            (drop_bit_word
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (nat_of_num (Bit0 (Bit0 (Bit0 One)))) i)
            (of_int
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
            (drop_bit_word
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One))))) i)
            (of_int
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
            (drop_bit_word
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One))))) i)
            (of_int
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))))];;

let rec u8_list_of_u16
  i = [cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
         (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (and_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))) i
           (of_int (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
             (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))));
        cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (and_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
            (drop_bit_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
              (nat_of_num (Bit0 (Bit0 (Bit0 One)))) i)
            (of_int (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
              (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))))];;

let rec storev
  mc m addr v =
    (match mc
      with M8 ->
        (match v with Vundef -> None
          | Vbyte n ->
            Some (fun i ->
                   (if equal_word
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         i addr
                     then Some n else m i))
          | Vshort _ -> None | Vint _ -> None | Vlong _ -> None)
      | M16 ->
        (match v with Vundef -> None | Vbyte _ -> None
          | Vshort n ->
            (let l = u8_list_of_u16 n in
              Some (fun i ->
                     (if equal_word
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                           i addr
                       then Some (nth l Zero_nat)
                       else (if equal_word
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                  i (plus_word
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                      addr
                                      (one_worda
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))))
                              then Some (nth l one_nat) else m i))))
          | Vint _ -> None | Vlong _ -> None)
      | M32 ->
        (match v with Vundef -> None | Vbyte _ -> None | Vshort _ -> None
          | Vint n ->
            (let l = u8_list_of_u32 n in
              Some (fun i ->
                     (if equal_word
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                           i addr
                       then Some (nth l Zero_nat)
                       else (if equal_word
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                  i (plus_word
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                      addr
                                      (one_worda
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))))
                              then Some (nth l one_nat)
                              else (if equal_word
 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))) i
 (plus_word
   (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
   addr
   (of_int
     (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
     (Pos (Bit0 One))))
                                     then Some (nth l (nat_of_num (Bit0 One)))
                                     else (if equal_word
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        i (plus_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            addr
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 One))))
    then Some (nth l (nat_of_num (Bit1 One))) else m i))))))
          | Vlong _ -> None)
      | M64 ->
        (match v with Vundef -> None | Vbyte _ -> None | Vshort _ -> None
          | Vint _ -> None
          | Vlong n ->
            (let l = u8_list_of_u64 n in
              Some (fun i ->
                     (if equal_word
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                           i addr
                       then Some (nth l Zero_nat)
                       else (if equal_word
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                  i (plus_word
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                      addr
                                      (one_worda
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))))
                              then Some (nth l one_nat)
                              else (if equal_word
 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))) i
 (plus_word
   (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
   addr
   (of_int
     (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
     (Pos (Bit0 One))))
                                     then Some (nth l (nat_of_num (Bit0 One)))
                                     else (if equal_word
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        i (plus_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            addr
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit1 One))))
    then Some (nth l (nat_of_num (Bit1 One)))
    else (if equal_word
               (len_bit0
                 (len_bit0
                   (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               i (plus_word
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   addr
                   (of_int
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     (Pos (Bit0 (Bit0 One)))))
           then Some (nth l (nat_of_num (Bit0 (Bit0 One))))
           else (if equal_word
                      (len_bit0
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                      i (plus_word
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                          addr
                          (of_int
                            (len_bit0
                              (len_bit0
                                (len_bit0
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                            (Pos (Bit1 (Bit0 One)))))
                  then Some (nth l (nat_of_num (Bit1 (Bit0 One))))
                  else (if equal_word
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             i (plus_word
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 len_num1))))))
                                 addr
                                 (of_int
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                   (Pos (Bit0 (Bit1 One)))))
                         then Some (nth l (nat_of_num (Bit0 (Bit1 One))))
                         else (if equal_word
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                    i (plus_word
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))) addr
(of_int
  (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
  (Pos (Bit1 (Bit1 One)))))
                                then Some (nth l (nat_of_num (Bit1 (Bit1 One))))
                                else m i))))))))))));;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec of_nat_aux _A inc x1 i = match inc, x1, i with inc, Zero_nat, i -> i
                        | inc, Suc n, i -> of_nat_aux _A inc n (inc i);;

let rec of_nata _A
  n = of_nat_aux _A
        (fun i ->
          plus _A.semiring_numeral_semiring_1.numeral_semiring_numeral.semigroup_add_numeral.plus_semigroup_add
            i (one _A.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral))
        n (zero _A.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero);;

let rec of_nat _A
  n = Word (take_bit_int (len_of _A.len0_len Type) (of_nata semiring_1_int n));;

let rec butlast = function [] -> []
                  | x :: xs -> (if null xs then [] else x :: butlast xs);;

let rec the_nat _A w = nat (the_int _A w);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec signed_take_bit _A
  n a = (let l =
           take_bit _A.semiring_bit_operations_ring_bit_operations (Suc n) a in
          (if bit _A.semiring_bit_operations_ring_bit_operations.semiring_bits_semiring_bit_operations
                l n
            then plus _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.numeral_neg_numeral.semigroup_add_numeral.plus_semigroup_add
                   l (push_bit _A.semiring_bit_operations_ring_bit_operations
                       (Suc n)
                       (uminus
                         _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.group_add_neg_numeral.uminus_group_add
                         (one _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.numeral_neg_numeral.one_numeral)))
            else l));;

let rec minus_nat m n = match m, n with Suc m, Suc n -> minus_nat m n
                    | Zero_nat, n -> Zero_nat
                    | m, Zero_nat -> m;;

let rec the_signed_int _A
  w = signed_take_bit ring_bit_operations_int
        (minus_nat (len_of _A.len0_len Type) (Suc Zero_nat)) (the_int _A w);;

let rec word_sle _A
  a b = less_eq_int (the_signed_int _A a) (the_signed_int _A b);;

let iNSN_SIZE : nat = nat_of_num (Bit0 (Bit0 (Bit0 One)));;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (Suc n) xs
                     | n, [] -> n;;

let rec word_sless _A
  a b = less_int (the_signed_int _A a) (the_signed_int _A b);;

let rec call_depth
  (Stack_state_ext (call_depth, stack_pointer, call_frames, more)) =
    call_depth;;

let rec stack_pointer_update
  stack_pointera
    (Stack_state_ext (call_depth, stack_pointer, call_frames, more)) =
    Stack_state_ext
      (call_depth, stack_pointera stack_pointer, call_frames, more);;

let rec stack_pointer
  (Stack_state_ext (call_depth, stack_pointer, call_frames, more)) =
    stack_pointer;;

let rec signed_cast _B _A
  w = Word (take_bit_int (len_of _A.len0_len Type) (the_signed_int _B w));;

let rec eval_add64_imm_R10
  i ss is_v1 =
    (let sp = stack_pointer ss in
      (if not is_v1
        then Some (stack_pointer_update
                    (fun _ ->
                      plus_word
                        (len_bit0
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                        sp (signed_cast
                             (len_signed
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             i))
                    ss)
        else None));;

let rec zero_word _A = Word Zero_int;;

let rec less_word _A a b = less_int (the_int _A a) (the_int _A b);;

let rec eval_load_imm
  dst imm1 imm2 rs =
    (let a =
       or_word
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (and_word
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
           (cast (len_signed
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             imm1)
           (of_int
             (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1
    (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1
  (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1
(Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1
    (Bit1 (Bit1 (Bit1 (Bit1 One))))))))))))))))))))))))))))))))))
         (push_bit_word
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
           (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
           (cast (len_signed
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             imm2))
       in
      fun_upd equal_bpf_ireg rs dst a);;

let rec divide_word _A
  a b = of_int _A (divide_inta (the_int _A a) (the_int _A b));;

let rec minus_word _A
  a b = of_int _A (minus_inta (the_int _A a) (the_int _A b));;

let rec u4_to_bpf_ireg
  dst = (if equal_word (len_bit0 (len_bit0 len_num1)) dst
              (zero_word (len_bit0 (len_bit0 len_num1)))
          then Some BR0
          else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                     (one_worda (len_bit0 (len_bit0 len_num1)))
                 then Some BR1
                 else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                            (of_int (len_bit0 (len_bit0 len_num1))
                              (Pos (Bit0 One)))
                        then Some BR2
                        else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                                   (of_int (len_bit0 (len_bit0 len_num1))
                                     (Pos (Bit1 One)))
                               then Some BR3
                               else (if equal_word
  (len_bit0 (len_bit0 len_num1)) dst
  (of_int (len_bit0 (len_bit0 len_num1)) (Pos (Bit0 (Bit0 One))))
                                      then Some BR4
                                      else (if equal_word
         (len_bit0 (len_bit0 len_num1)) dst
         (of_int (len_bit0 (len_bit0 len_num1)) (Pos (Bit1 (Bit0 One))))
     then Some BR5
     else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                (of_int (len_bit0 (len_bit0 len_num1)) (Pos (Bit0 (Bit1 One))))
            then Some BR6
            else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                       (of_int (len_bit0 (len_bit0 len_num1))
                         (Pos (Bit1 (Bit1 One))))
                   then Some BR7
                   else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                              (of_int (len_bit0 (len_bit0 len_num1))
                                (Pos (Bit0 (Bit0 (Bit0 One)))))
                          then Some BR8
                          else (if equal_word (len_bit0 (len_bit0 len_num1)) dst
                                     (of_int (len_bit0 (len_bit0 len_num1))
                                       (Pos (Bit1 (Bit0 (Bit0 One)))))
                                 then Some BR9
                                 else (if equal_word
    (len_bit0 (len_bit0 len_num1)) dst
    (of_int (len_bit0 (len_bit0 len_num1)) (Pos (Bit0 (Bit1 (Bit0 One)))))
then Some BR10 else None)))))))))));;

let rec call_frames
  (Stack_state_ext (call_depth, stack_pointer, call_frames, more)) =
    call_frames;;

let rec eval_reg dst rs = rs dst;;

let rec list_update
  x0 i y = match x0, i, y with x :: xs, Suc i, y -> x :: list_update xs i y
    | x :: xs, Zero_nat, y -> y :: xs
    | [], i, y -> [];;

let rec push_frame
  rs ss is_v1 pc enable_stack_frame_gaps =
    (let npc =
       plus_word
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         pc (one_worda
              (len_bit0
                (len_bit0
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
       in
     let fp = eval_reg BR10 rs in
     let caller =
       [eval_reg BR6 rs; eval_reg BR7 rs; eval_reg BR8 rs; eval_reg BR9 rs] in
     let frame = CallFrame_ext (caller, fp, npc, ()) in
     let update1 =
       plus_word
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (call_depth ss)
         (one_worda
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
       in
      (if equal_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            update1
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))
        then (None, rs)
        else (let update2 =
                (if is_v1
                  then (if enable_stack_frame_gaps
                         then plus_word
                                (len_bit0
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 len_num1))))))
                                (stack_pointer ss)
                                (times_worda
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                  (of_int
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                    (Pos (Bit0
   (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))))))
                                  (of_int
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                    (Pos (Bit0 One))))
                         else plus_word
                                (len_bit0
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 len_num1))))))
                                (stack_pointer ss)
                                (of_int
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                  (Pos (Bit0
 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
     (Bit0 (Bit0 (Bit0 One)))))))))))))))
                  else stack_pointer ss)
                in
              let update3 =
                list_update (call_frames ss)
                  (the_nat
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    (call_depth ss))
                  frame
                in
              let stack = Some (Stack_state_ext (update1, update2, update3, ()))
                in
              let a = fun_upd equal_bpf_ireg rs BR10 update2 in
               (stack, a))));;

let rec eval_call_reg
  src imm rs ss is_v1 pc fm enable_stack_frame_gaps program_vm_addr =
    (match
      u4_to_bpf_ireg
        (cast (len_signed
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 len_num1)) imm)
      with None -> None
      | Some iv ->
        (let pc1 = (if is_v1 then eval_reg iv rs else eval_reg src rs) in
          (match push_frame rs ss is_v1 pc enable_stack_frame_gaps
            with (None, _) -> None
            | (Some ssa, rsa) ->
              (if less_word
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    pc1 program_vm_addr
                then None
                else (let next_pc =
                        divide_word
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                          (minus_word
                            (len_bit0
                              (len_bit0
                                (len_bit0
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                            pc1 program_vm_addr)
                          (of_nat
                            (len_bit0
                              (len_bit0
                                (len_bit0
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                            iNSN_SIZE)
                        in
                       Some (next_pc, (rsa, ssa)))))));;

let rec get_function_registry key fm = fm key;;

let rec eval_call_imm
  pc src imm rs ss is_v1 fm enable_stack_frame_gaps =
    (match
      (if equal_bpf_irega src BR0
        then get_function_registry
               (cast (len_signed
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                 imm)
               fm
        else Some (cast (len_signed
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    imm))
      with None -> None
      | Some npc ->
        (match push_frame rs ss is_v1 pc enable_stack_frame_gaps
          with (None, _) -> None | (Some ssa, rsa) -> Some (npc, (rsa, ssa))));;

let rec eval_snd_op_u64
  x0 uu = match x0, uu with
    SOImm i, uu ->
      signed_cast
        (len_signed
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        i
    | SOReg r, rs -> rs r;;

let rec eval_pqr64_2
  pop2 dst sop rs is_v1 =
    (if is_v1 then OKN
      else (let dv_u =
              cast (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                (len_bit0
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                (eval_reg dst rs)
              in
            let sv_u =
              cast (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                (len_bit0
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                (eval_snd_op_u64 sop rs)
              in
            let dv_i =
              cast (len_signed
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                (len_bit0
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                (signed_cast
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (len_signed
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                  (eval_reg dst rs))
              in
            let sv_i =
              cast (len_signed
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                (len_bit0
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                (signed_cast
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (len_signed
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                  (eval_reg dst rs))
              in
             (match pop2
               with BPF_UHMUL ->
                 OKS (fun_upd equal_bpf_ireg rs dst
                       (drop_bit_word
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (nat_of_num
                           (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
                         (cast (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 len_num1)))))))
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                           (times_worda
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1)))))))
                             dv_u sv_u))))
               | BPF_SHMUL ->
                 OKS (fun_upd equal_bpf_ireg rs dst
                       (drop_bit_word
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (nat_of_num
                           (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
                         (cast (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 len_num1)))))))
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                           (times_worda
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1)))))))
                             dv_i sv_i)))))));;

let rec eval_store
  chk dst sop off rs mem =
    (let dv =
       signed_cast
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (len_signed
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
         (eval_reg dst rs)
       in
     let vm_addr =
       cast (len_signed
              (len_bit0
                (len_bit0
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (plus_word
           (len_signed
             (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
           dv (signed_cast
                (len_signed
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                (len_signed
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                off))
       in
     let sv = eval_snd_op_u64 sop rs in
      storev chk mem vm_addr (memory_chunk_value_of_u64 chk sv));;

let rec modulo_word _A
  a b = of_int _A (modulo_inta (the_int _A a) (the_int _A b));;

let rec eval_snd_op_i64
  x0 uu = match x0, uu with
    SOImm i, uu ->
      signed_cast
        (len_signed
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (len_signed
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
        i
    | SOReg r, rs ->
        signed_cast
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_signed
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
          (rs r);;

let rec eval_pqr64_aux2
  pop dst sop rs =
    (let dv =
       signed_cast
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (len_signed
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
         (eval_reg dst rs)
       in
     let sv = eval_snd_op_i64 sop rs in
      (match pop with BPF_LMUL -> OKN | BPF_UDIV -> OKN | BPF_UREM -> OKN
        | BPF_SDIV ->
          (if equal_word
                (len_signed
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                sv (zero_word
                     (len_signed
                       (len_bit0
                         (len_bit0
                           (len_bit0
                             (len_bit0 (len_bit0 (len_bit0 len_num1))))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (cast (len_signed
                               (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1)))))))
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (divide_word
                           (len_signed
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                           dv sv))))
        | BPF_SREM ->
          (if equal_word
                (len_signed
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                sv (zero_word
                     (len_signed
                       (len_bit0
                         (len_bit0
                           (len_bit0
                             (len_bit0 (len_bit0 (len_bit0 len_num1))))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (cast (len_signed
                               (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1)))))))
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (modulo_word
                           (len_signed
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                           dv sv))))));;

let rec eval_pqr64_aux1
  pop dst sop rs =
    (let dv = eval_reg dst rs in
     let sv = eval_snd_op_u64 sop rs in
      (match pop
        with BPF_LMUL ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (cast (len_bit0
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (times_worda
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    dv sv)))
        | BPF_UDIV ->
          (if equal_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                sv (zero_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (cast (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (divide_word
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                           dv sv))))
        | BPF_UREM ->
          (if equal_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                sv (zero_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (cast (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (modulo_word
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                           dv sv))))
        | BPF_SDIV -> OKN | BPF_SREM -> OKN));;

let rec eval_pqr64
  pop dst sop rs is_v1 =
    (if is_v1 then OKN
      else (match pop with BPF_LMUL -> eval_pqr64_aux1 pop dst sop rs
             | BPF_UDIV -> eval_pqr64_aux1 pop dst sop rs
             | BPF_UREM -> eval_pqr64_aux1 pop dst sop rs
             | BPF_SDIV -> eval_pqr64_aux2 pop dst sop rs
             | BPF_SREM -> eval_pqr64_aux2 pop dst sop rs));;

let rec eval_snd_op_u32
  x0 uu = match x0, uu with
    SOImm i, uu ->
      cast (len_signed
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) i
    | SOReg r, rs ->
        cast (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          (rs r);;

let rec eval_pqr32_aux2
  pop dst sop rs =
    (let dv =
       cast (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
         (eval_reg dst rs)
       in
     let sv = eval_snd_op_u32 sop rs in
      (match pop with BPF_LMUL -> OKN
        | BPF_UDIV ->
          (if equal_word
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                sv (zero_word
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (cast (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (divide_word
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                           dv sv))))
        | BPF_UREM ->
          (if equal_word
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                sv (zero_word
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (cast (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (modulo_word
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                           dv sv))))
        | BPF_SDIV -> OKN | BPF_SREM -> OKN));;

let rec eval_snd_op_i32
  x0 uu = match x0, uu with
    SOImm i, uu ->
      signed_cast
        (len_signed
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (len_signed
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        i
    | SOReg r, rs ->
        signed_cast
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (len_signed
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (rs r);;

let rec eval_pqr32_aux1
  pop dst sop rs =
    (let dv =
       signed_cast
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (len_signed
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (eval_reg dst rs)
       in
     let sv = eval_snd_op_i32 sop rs in
      (match pop
        with BPF_LMUL ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (cast (len_signed
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (times_worda
                    (len_signed
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    dv sv)))
        | BPF_UDIV -> OKN | BPF_UREM -> OKN
        | BPF_SDIV ->
          (if equal_word
                (len_signed
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                sv (zero_word
                     (len_signed
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (cast (len_signed
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (divide_word
                           (len_signed
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                           dv sv))))
        | BPF_SREM ->
          (if equal_word
                (len_signed
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                sv (zero_word
                     (len_signed
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (cast (len_signed
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (modulo_word
                           (len_signed
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                           dv sv))))));;

let rec eval_pqr32
  pop dst sop rs is_v1 =
    (if is_v1 then OKN
      else (match pop with BPF_LMUL -> eval_pqr32_aux1 pop dst sop rs
             | BPF_UDIV -> eval_pqr32_aux2 pop dst sop rs
             | BPF_UREM -> eval_pqr32_aux2 pop dst sop rs
             | BPF_SDIV -> eval_pqr32_aux1 pop dst sop rs
             | BPF_SREM -> eval_pqr32_aux1 pop dst sop rs));;

let rec uminus_word _A a = of_int _A (uminus_inta (the_int _A a));;

let rec eval_neg64
  dst rs is_v1 =
    (if is_v1
      then (let dv =
              signed_cast
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                (len_signed
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                (eval_reg dst rs)
              in
             OKS (fun_upd equal_bpf_ireg rs dst
                   (cast (len_signed
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     (uminus_word
                       (len_signed
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                       dv))))
      else OKN);;

let u32_MAX : num1 bit0 bit0 bit0 bit0 bit0 word
  = of_int (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
      (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1
   (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1
 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1
     (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1
   (Bit1 (Bit1 (Bit1 One))))))))))))))))))))))))))))))));;

let rec eval_neg32
  dst rs is_v1 =
    (if is_v1
      then (let dv =
              signed_cast
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                (len_signed
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                (eval_reg dst rs)
              in
             OKS (fun_upd equal_bpf_ireg rs dst
                   (and_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     (cast (len_signed
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                       (len_bit0
                         (len_bit0
                           (len_bit0
                             (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                       (uminus_word
                         (len_signed
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         dv))
                     (cast (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                       (len_bit0
                         (len_bit0
                           (len_bit0
                             (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                       u32_MAX))))
      else OKN);;

let rec eval_hor64
  dst imm rs is_v1 =
    (if is_v1 then OKN
      else (let dv = eval_reg dst rs in
            let dv2 =
              or_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                dv (push_bit_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                     (cast (len_signed
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                       (len_bit0
                         (len_bit0
                           (len_bit0
                             (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                       imm))
              in
             OKS (fun_upd equal_bpf_ireg rs dst dv2)));;

let rec bit_word _A
  a n = equal_word _A (and_word _A (drop_bit_word _A n a) (one_worda _A))
          (one_worda _A);;

let rec arsh64
  x n = (if bit_word
              (len_signed
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
              x (nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))
          then or_word
                 (len_signed
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                 (drop_bit_word
                   (len_signed
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                   n x)
                 (push_bit_word
                   (len_signed
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                   (minus_nat
                     (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
                     n)
                   (minus_word
                     (len_signed
                       (len_bit0
                         (len_bit0
                           (len_bit0
                             (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                     (power
                       (power_word
                         (len_signed
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))))
                       (of_int
                         (len_signed
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                         (Pos (Bit0 One)))
                       n)
                     (one_worda
                       (len_signed
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))))))
          else drop_bit_word
                 (len_signed
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                 n x);;

let rec eval_alu64_aux3
  bop dst sop rs =
    (let dv =
       signed_cast
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (len_signed
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
         (eval_reg dst rs)
       in
     let sv =
       and_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
         (eval_snd_op_u32 sop rs)
         (of_int (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
           (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
       in
      (match bop with BPF_ADD -> OKN | BPF_SUB -> OKN | BPF_MUL -> OKN
        | BPF_DIV -> OKN | BPF_OR -> OKN | BPF_AND -> OKN | BPF_LSH -> OKN
        | BPF_RSH -> OKN | BPF_MOD -> OKN | BPF_XOR -> OKN | BPF_MOV -> OKN
        | BPF_ARSH ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (cast (len_signed
                        (len_bit0
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (arsh64 dv
                    (the_nat
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                      sv))))));;

let rec eval_alu64_aux2
  bop dst sop rs =
    (let dv = eval_reg dst rs in
     let sv =
       and_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
         (eval_snd_op_u32 sop rs)
         (of_int (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
           (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
       in
      (match bop with BPF_ADD -> OKN | BPF_SUB -> OKN | BPF_MUL -> OKN
        | BPF_DIV -> OKN | BPF_OR -> OKN | BPF_AND -> OKN
        | BPF_LSH ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (push_bit_word
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (the_nat
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    sv)
                  dv))
        | BPF_RSH ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (drop_bit_word
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (the_nat
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    sv)
                  dv))
        | BPF_MOD -> OKN | BPF_XOR -> OKN | BPF_MOV -> OKN | BPF_ARSH -> OKN));;

let rec xor_word _A v w = Word (xor_int (the_int _A v) (the_int _A w));;

let rec eval_alu64_aux1
  bop dst sop rs is_v1 =
    (let dv = eval_reg dst rs in
     let sv = eval_snd_op_u64 sop rs in
      (match bop
        with BPF_ADD ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (plus_word
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  dv sv))
        | BPF_SUB ->
          (match sop
            with SOImm _ ->
              (if is_v1
                then OKS (fun_upd equal_bpf_ireg rs dst
                           (minus_word
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             dv sv))
                else OKS (fun_upd equal_bpf_ireg rs dst
                           (minus_word
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             sv dv)))
            | SOReg _ ->
              OKS (fun_upd equal_bpf_ireg rs dst
                    (minus_word
                      (len_bit0
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                      dv sv)))
        | BPF_MUL ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (times_worda
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  dv sv))
        | BPF_DIV ->
          (if equal_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                sv (zero_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (divide_word
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         dv sv)))
        | BPF_OR ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (or_word
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  dv sv))
        | BPF_AND ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (and_word
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  dv sv))
        | BPF_LSH -> OKN | BPF_RSH -> OKN
        | BPF_MOD ->
          (if equal_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                sv (zero_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (modulo_word
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         dv sv)))
        | BPF_XOR ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (xor_word
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  dv sv))
        | BPF_MOV -> OKS (fun_upd equal_bpf_ireg rs dst sv)
        | BPF_ARSH -> OKN));;

let rec eval_alu64
  bop dst sop rs is_v1 =
    (match bop with BPF_ADD -> eval_alu64_aux1 bop dst sop rs is_v1
      | BPF_SUB -> eval_alu64_aux1 bop dst sop rs is_v1
      | BPF_MUL -> (if is_v1 then eval_alu64_aux1 bop dst sop rs is_v1 else OKN)
      | BPF_DIV -> (if is_v1 then eval_alu64_aux1 bop dst sop rs is_v1 else OKN)
      | BPF_OR -> eval_alu64_aux1 bop dst sop rs is_v1
      | BPF_AND -> eval_alu64_aux1 bop dst sop rs is_v1
      | BPF_LSH -> eval_alu64_aux2 bop dst sop rs
      | BPF_RSH -> eval_alu64_aux2 bop dst sop rs
      | BPF_MOD -> (if is_v1 then eval_alu64_aux1 bop dst sop rs is_v1 else OKN)
      | BPF_XOR -> eval_alu64_aux1 bop dst sop rs is_v1
      | BPF_MOV -> eval_alu64_aux1 bop dst sop rs is_v1
      | BPF_ARSH -> eval_alu64_aux3 bop dst sop rs);;

let rec arsh32
  x n = (if bit_word
              (len_signed
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              x (nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 One)))))
          then or_word
                 (len_signed
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 (drop_bit_word
                   (len_signed
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   n x)
                 (push_bit_word
                   (len_signed
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   (minus_nat
                     (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) n)
                   (minus_word
                     (len_signed
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     (power
                       (power_word
                         (len_signed
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                       (of_int
                         (len_signed
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (Pos (Bit0 One)))
                       n)
                     (one_worda
                       (len_signed
                         (len_bit0
                           (len_bit0
                             (len_bit0 (len_bit0 (len_bit0 len_num1)))))))))
          else drop_bit_word
                 (len_signed
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 n x);;

let rec eval_alu32_aux3
  bop dst sop rs =
    (let dv =
       signed_cast
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (len_signed
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (eval_reg dst rs)
       in
     let sv =
       and_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
         (eval_snd_op_u32 sop rs)
         (of_int (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
           (Pos (Bit1 (Bit1 (Bit1 (Bit1 One))))))
       in
      (match bop with BPF_ADD -> OKN | BPF_SUB -> OKN | BPF_MUL -> OKN
        | BPF_DIV -> OKN | BPF_OR -> OKN | BPF_AND -> OKN | BPF_LSH -> OKN
        | BPF_RSH -> OKN | BPF_MOD -> OKN | BPF_XOR -> OKN | BPF_MOV -> OKN
        | BPF_ARSH ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (and_word
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (cast (len_signed
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    (arsh32 dv
                      (the_nat
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        sv)))
                  (cast (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    u32_MAX)))));;

let rec eval_alu32_aux2
  bop dst sop rs =
    (let dv =
       cast (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
         (eval_reg dst rs)
       in
     let sv = eval_snd_op_u32 sop rs in
      (match bop with BPF_ADD -> OKN | BPF_SUB -> OKN | BPF_MUL -> OKN
        | BPF_DIV ->
          (if equal_word
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                sv (zero_word
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (cast (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (divide_word
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                           dv sv))))
        | BPF_OR ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (cast (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (or_word
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    dv sv)))
        | BPF_AND ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (cast (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (and_word
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    dv sv)))
        | BPF_LSH ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (cast (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (push_bit_word
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    (the_nat
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                      (and_word
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        sv (of_int
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                             (Pos (Bit1 (Bit1 (Bit1 (Bit1 One))))))))
                    dv)))
        | BPF_RSH ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (cast (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (drop_bit_word
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    (the_nat
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                      (and_word
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        sv (of_int
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                             (Pos (Bit1 (Bit1 (Bit1 (Bit1 One))))))))
                    dv)))
        | BPF_MOD ->
          (if equal_word
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                sv (zero_word
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            then (match sop with SOImm _ -> NOK | SOReg _ -> OKN)
            else OKS (fun_upd equal_bpf_ireg rs dst
                       (cast (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (modulo_word
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                           dv sv))))
        | BPF_XOR ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (cast (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (xor_word
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    dv sv)))
        | BPF_MOV ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (cast (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  sv))
        | BPF_ARSH -> OKN));;

let rec eval_alu32_aux1
  bop dst sop rs is_v1 =
    (let dv =
       signed_cast
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (len_signed
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (eval_reg dst rs)
       in
     let sv = eval_snd_op_i32 sop rs in
      (match bop
        with BPF_ADD ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (signed_cast
                  (len_signed
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (plus_word
                    (len_signed
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    dv sv)))
        | BPF_SUB ->
          (match sop
            with SOImm _ ->
              (if is_v1
                then OKS (fun_upd equal_bpf_ireg rs dst
                           (signed_cast
                             (len_signed
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             (minus_word
                               (len_signed
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1))))))
                               dv sv)))
                else OKS (fun_upd equal_bpf_ireg rs dst
                           (signed_cast
                             (len_signed
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             (minus_word
                               (len_signed
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1))))))
                               sv dv))))
            | SOReg _ ->
              OKS (fun_upd equal_bpf_ireg rs dst
                    (signed_cast
                      (len_signed
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                      (len_bit0
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                      (minus_word
                        (len_signed
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                        dv sv))))
        | BPF_MUL ->
          OKS (fun_upd equal_bpf_ireg rs dst
                (signed_cast
                  (len_signed
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (times_worda
                    (len_signed
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    dv sv)))
        | BPF_DIV -> OKN | BPF_OR -> OKN | BPF_AND -> OKN | BPF_LSH -> OKN
        | BPF_RSH -> OKN | BPF_MOD -> OKN | BPF_XOR -> OKN | BPF_MOV -> OKN
        | BPF_ARSH -> OKN));;

let rec eval_alu32
  bop dst sop rs is_v1 =
    (match bop with BPF_ADD -> eval_alu32_aux1 bop dst sop rs is_v1
      | BPF_SUB -> eval_alu32_aux1 bop dst sop rs is_v1
      | BPF_MUL -> (if is_v1 then eval_alu32_aux1 bop dst sop rs is_v1 else OKN)
      | BPF_DIV -> (if is_v1 then eval_alu32_aux2 bop dst sop rs else OKN)
      | BPF_OR -> eval_alu32_aux2 bop dst sop rs
      | BPF_AND -> eval_alu32_aux2 bop dst sop rs
      | BPF_LSH -> eval_alu32_aux2 bop dst sop rs
      | BPF_RSH -> eval_alu32_aux2 bop dst sop rs
      | BPF_MOD -> (if is_v1 then eval_alu32_aux2 bop dst sop rs else OKN)
      | BPF_XOR -> eval_alu32_aux2 bop dst sop rs
      | BPF_MOV -> eval_alu32_aux2 bop dst sop rs
      | BPF_ARSH -> eval_alu32_aux3 bop dst sop rs);;

let rec eval_load
  chk dst sop off rs mem =
    (let sv = eval_snd_op_u64 (SOReg sop) rs in
     let vm_addr =
       plus_word
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         sv (signed_cast
              (len_signed (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              off)
       in
      (match loadv chk mem vm_addr with None -> None | Some Vundef -> None
        | Some (Vbyte v) ->
          Some (fun_upd equal_bpf_ireg rs dst
                 (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   v))
        | Some (Vshort v) ->
          Some (fun_upd equal_bpf_ireg rs dst
                 (cast (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   v))
        | Some (Vint v) ->
          Some (fun_upd equal_bpf_ireg rs dst
                 (cast (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   v))
        | Some (Vlong v) -> Some (fun_upd equal_bpf_ireg rs dst v)));;

let rec caller_saved_registers
  (CallFrame_ext (caller_saved_registers, frame_pointer, target_pc, more)) =
    caller_saved_registers;;

let rec frame_pointer
  (CallFrame_ext (caller_saved_registers, frame_pointer, target_pc, more)) =
    frame_pointer;;

let rec target_pc
  (CallFrame_ext (caller_saved_registers, frame_pointer, target_pc, more)) =
    target_pc;;

let rec pop_frame
  ss = nth (call_frames ss)
         (the_nat
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
           (minus_word
             (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             (call_depth ss)
             (one_worda
               (len_bit0
                 (len_bit0
                   (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))));;

let rec eval_exit
  rs ss is_v1 =
    (let x =
       minus_word
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (call_depth ss)
         (one_worda
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
       in
     let frame = pop_frame ss in
     let rsa =
       fun_upd equal_bpf_ireg
         (fun_upd equal_bpf_ireg
           (fun_upd equal_bpf_ireg
             (fun_upd equal_bpf_ireg
               (fun_upd equal_bpf_ireg rs BR10 (frame_pointer frame)) BR9
               (nth (caller_saved_registers frame) (nat_of_num (Bit1 One))))
             BR8 (nth (caller_saved_registers frame) (nat_of_num (Bit0 One))))
           BR7 (nth (caller_saved_registers frame) one_nat))
         BR6 (nth (caller_saved_registers frame) Zero_nat)
       in
     let y =
       (if is_v1
         then minus_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                (stack_pointer ss)
                (times_worda
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (of_int
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    (Pos (Bit0 One)))
                  (of_int
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    (Pos (Bit0 (Bit0 (Bit0 (Bit0
     (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))))))))
         else stack_pointer ss)
       in
     let z = butlast (call_frames ss) in
     let ssa = Stack_state_ext (x, y, z, ()) in
     let pc = target_pc frame in
      (pc, (rsa, ssa)));;

let rec less_eq_word _A a b = less_eq_int (the_int _A a) (the_int _A b);;

let rec eval_jmp
  cond dst sop rs =
    (let udv = eval_reg dst rs in
     let usv = eval_snd_op_u64 sop rs in
     let sdv =
       signed_cast
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
         (len_signed
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
         udv
       in
     let ssv = eval_snd_op_i64 sop rs in
      (match cond
        with Eq ->
          equal_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            udv usv
        | Gt ->
          less_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            usv udv
        | Ge ->
          less_eq_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            usv udv
        | Lt ->
          less_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            udv usv
        | Le ->
          less_eq_word
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            udv usv
        | SEt ->
          not (equal_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                (and_word
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  udv usv)
                (zero_word
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))))
        | Ne ->
          not (equal_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                udv usv)
        | SGt ->
          word_sless
            (len_signed
              (len_bit0
                (len_bit0
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
            ssv sdv
        | SGe ->
          word_sle
            (len_signed
              (len_bit0
                (len_bit0
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
            ssv sdv
        | SLt ->
          word_sless
            (len_signed
              (len_bit0
                (len_bit0
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
            sdv ssv
        | SLe ->
          word_sle
            (len_signed
              (len_bit0
                (len_bit0
                  (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
            sdv ssv));;

let rec size_list x = gen_length Zero_nat x;;

let rec equal_nat x0 x1 = match x0, x1 with Zero_nat, Suc x2 -> false
                    | Suc x2, Zero_nat -> false
                    | Suc x2, Suc y2 -> equal_nat x2 y2
                    | Zero_nat, Zero_nat -> true;;

let rec u64_of_u8_list
  l = (if not (equal_nat (size_list l) (nat_of_num (Bit0 (Bit0 (Bit0 One)))))
        then None
        else Some (or_word
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                    (push_bit_word
                      (len_bit0
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                      (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One))))))
                      (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (len_bit0
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                        (nth l (nat_of_num (Bit1 (Bit1 One))))))
                    (or_word
                      (len_bit0
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                      (push_bit_word
                        (len_bit0
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                        (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))))
                        (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                          (nth l (nat_of_num (Bit0 (Bit1 One))))))
                      (or_word
                        (len_bit0
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                        (push_bit_word
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                          (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))
                          (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (len_bit0
                              (len_bit0
                                (len_bit0
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                            (nth l (nat_of_num (Bit1 (Bit0 One))))))
                        (or_word
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                          (push_bit_word
                            (len_bit0
                              (len_bit0
                                (len_bit0
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                            (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                            (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                              (len_bit0
                                (len_bit0
                                  (len_bit0
                                    (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                              (nth l (nat_of_num (Bit0 (Bit0 One))))))
                          (or_word
                            (len_bit0
                              (len_bit0
                                (len_bit0
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                            (push_bit_word
                              (len_bit0
                                (len_bit0
                                  (len_bit0
                                    (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One)))))
                              (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                (len_bit0
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 len_num1))))))
                                (nth l (nat_of_num (Bit1 One)))))
                            (or_word
                              (len_bit0
                                (len_bit0
                                  (len_bit0
                                    (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                              (push_bit_word
                                (len_bit0
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 len_num1))))))
                                (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One)))))
                                (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                  (nth l (nat_of_num (Bit0 One)))))
                              (or_word
                                (len_bit0
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 len_num1))))))
                                (push_bit_word
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                  (nat_of_num (Bit0 (Bit0 (Bit0 One))))
                                  (cast (len_bit0
  (len_bit0 (len_bit0 len_num1)))
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                    (nth l one_nat)))
                                (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                  (nth l Zero_nat))))))))));;

let rec u32_of_u8_list
  l = (if not (equal_nat (size_list l) (nat_of_num (Bit0 (Bit0 One)))) then None
        else Some (or_word
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                    (push_bit_word
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                      (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One)))))
                      (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        (nth l (nat_of_num (Bit1 One)))))
                    (or_word
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                      (push_bit_word
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One)))))
                        (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (nth l (nat_of_num (Bit0 One)))))
                      (or_word
                        (len_bit0
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        (push_bit_word
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (nat_of_num (Bit0 (Bit0 (Bit0 One))))
                          (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                            (nth l one_nat)))
                        (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                          (nth l Zero_nat))))));;

let rec u16_of_u8_list
  l = (if not (equal_nat (size_list l) (nat_of_num (Bit0 One))) then None
        else Some (or_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                    (push_bit_word
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                      (nat_of_num (Bit0 (Bit0 (Bit0 One))))
                      (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                        (nth l one_nat)))
                    (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                      (nth l Zero_nat))));;

let rec eval_le
  dst imm rs is_v1 =
    (if is_v1
      then (let dv = eval_reg dst rs in
             (if equal_word
                   (len_signed
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   imm (of_int
                         (len_signed
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (Pos (Bit0 (Bit0 (Bit0 (Bit0 One))))))
               then (match
                      u16_of_u8_list
                        (u8_list_of_u16
                          (cast (len_bit0
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 len_num1))))))
                            (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                            dv))
                      with None -> OKN
                      | Some v ->
                        OKS (fun_upd equal_bpf_ireg rs dst
                              (cast (len_bit0
                                      (len_bit0 (len_bit0 (len_bit0 len_num1))))
                                (len_bit0
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 len_num1))))))
                                v)))
               else (if equal_word
                          (len_signed
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                          imm (of_int
                                (len_signed
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 len_num1))))))
                                (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
                      then (match
                             u32_of_u8_list
                               (u8_list_of_u32
                                 (cast (len_bit0
 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 len_num1)))))
                                   dv))
                             with None -> OKN
                             | Some v ->
                               OKS (fun_upd equal_bpf_ireg rs dst
                                     (cast (len_bit0
     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                                       (len_bit0
 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                       v)))
                      else (if equal_word
                                 (len_signed
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 len_num1))))))
                                 imm (of_int
                                       (len_signed
 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                       (Pos
 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))
                             then (match u64_of_u8_list (u8_list_of_u64 dv)
                                    with None -> OKN
                                    | Some v ->
                                      OKS (fun_upd equal_bpf_ireg rs dst v))
                             else OKN))))
      else OKN);;

let rec eval_be
  dst imm rs is_v1 =
    (if is_v1
      then (let dv = eval_reg dst rs in
             (if equal_word
                   (len_signed
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   imm (of_int
                         (len_signed
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         (Pos (Bit0 (Bit0 (Bit0 (Bit0 One))))))
               then (match
                      u16_of_u8_list
                        (rev (u8_list_of_u16
                               (cast (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))
                                 dv)))
                      with None -> OKN
                      | Some v ->
                        OKS (fun_upd equal_bpf_ireg rs dst
                              (cast (len_bit0
                                      (len_bit0 (len_bit0 (len_bit0 len_num1))))
                                (len_bit0
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 len_num1))))))
                                v)))
               else (if equal_word
                          (len_signed
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                          imm (of_int
                                (len_signed
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 len_num1))))))
                                (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
                      then (match
                             u32_of_u8_list
                               (rev (u8_list_of_u32
                                      (cast
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) dv)))
                             with None -> OKN
                             | Some v ->
                               OKS (fun_upd equal_bpf_ireg rs dst
                                     (cast (len_bit0
     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                                       (len_bit0
 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                       v)))
                      else (if equal_word
                                 (len_signed
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0
 (len_bit0 (len_bit0 len_num1))))))
                                 imm (of_int
                                       (len_signed
 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                                       (Pos
 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))
                             then (match
                                    u64_of_u8_list
                                      (rev
(u8_list_of_u64
  (cast (len_bit0
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
    dv)))
                                    with None -> OKN
                                    | Some v ->
                                      OKS (fun_upd equal_bpf_ireg rs dst v))
                             else OKN))))
      else OKN);;

let rec step
  pc ins rs m ss sv fm enable_stack_frame_gaps program_vm_addr cur_cu remain_cu
    = (let is_v1 = (match sv with V1 -> true | V2 -> false) in
        (match ins
          with BPF_LD_IMM (dst, imm1, imm2) ->
            (let rsa = eval_load_imm dst imm1 imm2 rs in
              BPF_OK
                (plus_word
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   pc (of_int
                        (len_bit0
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                        (Pos (Bit0 One))),
                  rsa, m, ss, sv, fm, cur_cu, remain_cu))
          | BPF_LDX (chk, dst, sop, off) ->
            (match eval_load chk dst sop off rs m with None -> BPF_EFlag
              | Some rsa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rsa, m, ss, sv, fm, cur_cu, remain_cu))
          | BPF_ST (chk, dst, sop, off) ->
            (match eval_store chk dst sop off rs m with None -> BPF_EFlag
              | Some ma ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rs, ma, ss, sv, fm, cur_cu, remain_cu))
          | BPF_ADD_STK i ->
            (match eval_add64_imm_R10 i ss is_v1 with None -> BPF_Err
              | Some ssa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rs, m, ssa, sv, fm, cur_cu, remain_cu))
          | BPF_ALU (bop, d, sop) ->
            (match eval_alu32 bop d sop rs is_v1 with NOK -> BPF_Err
              | OKS rsa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rsa, m, ss, sv, fm, cur_cu, remain_cu)
              | OKN -> BPF_EFlag)
          | BPF_NEG32_REG dst ->
            (match eval_neg32 dst rs is_v1 with NOK -> BPF_Err
              | OKS rsa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rsa, m, ss, sv, fm, cur_cu, remain_cu)
              | OKN -> BPF_EFlag)
          | BPF_LE (dst, imm) ->
            (match eval_le dst imm rs is_v1 with NOK -> BPF_Err
              | OKS rsa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rsa, m, ss, sv, fm, cur_cu, remain_cu)
              | OKN -> BPF_EFlag)
          | BPF_BE (dst, imm) ->
            (match eval_be dst imm rs is_v1 with NOK -> BPF_Err
              | OKS rsa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rsa, m, ss, sv, fm, cur_cu, remain_cu)
              | OKN -> BPF_EFlag)
          | BPF_ALU64 (bop, d, sop) ->
            (match eval_alu64 bop d sop rs is_v1 with NOK -> BPF_Err
              | OKS rsa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rsa, m, ss, sv, fm, cur_cu, remain_cu)
              | OKN -> BPF_EFlag)
          | BPF_NEG64_REG dst ->
            (match eval_neg64 dst rs is_v1 with NOK -> BPF_Err
              | OKS rsa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rsa, m, ss, sv, fm, cur_cu, remain_cu)
              | OKN -> BPF_EFlag)
          | BPF_HOR64_IMM (dst, imm) ->
            (match eval_hor64 dst imm rs is_v1 with NOK -> BPF_Err
              | OKS rsa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rsa, m, ss, sv, fm, cur_cu, remain_cu)
              | OKN -> BPF_EFlag)
          | BPF_PQR (pop, dst, sop) ->
            (match eval_pqr32 pop dst sop rs is_v1 with NOK -> BPF_Err
              | OKS rsa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rsa, m, ss, sv, fm, cur_cu, remain_cu)
              | OKN -> BPF_EFlag)
          | BPF_PQR64 (pop, dst, sop) ->
            (match eval_pqr64 pop dst sop rs is_v1 with NOK -> BPF_Err
              | OKS rsa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rsa, m, ss, sv, fm, cur_cu, remain_cu)
              | OKN -> BPF_EFlag)
          | BPF_PQR2 (pop, dst, sop) ->
            (match eval_pqr64_2 pop dst sop rs is_v1 with NOK -> BPF_Err
              | OKS rsa ->
                BPF_OK
                  (plus_word
                     (len_bit0
                       (len_bit0
                         (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                     pc (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                    rsa, m, ss, sv, fm, cur_cu, remain_cu)
              | OKN -> BPF_EFlag)
          | BPF_JA off ->
            BPF_OK
              (plus_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 (plus_word
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   pc (signed_cast
                        (len_signed
                          (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                        (len_bit0
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                        off))
                 (one_worda
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                rs, m, ss, sv, fm, cur_cu, remain_cu)
          | BPF_JUMP (cond, bpf_ireg, snd_op, off) ->
            (if eval_jmp cond bpf_ireg snd_op rs
              then BPF_OK
                     (plus_word
                        (len_bit0
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                        (plus_word
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                          pc (signed_cast
                               (len_signed
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                               (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1))))))
                               off))
                        (one_worda
                          (len_bit0
                            (len_bit0
                              (len_bit0
                                (len_bit0 (len_bit0 (len_bit0 len_num1))))))),
                       rs, m, ss, sv, fm, cur_cu, remain_cu)
              else BPF_OK
                     (plus_word
                        (len_bit0
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                        pc (one_worda
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0 (len_bit0 len_num1))))))),
                       rs, m, ss, sv, fm, cur_cu, remain_cu))
          | BPF_CALL_REG (src, imm) ->
            (match
              eval_call_reg src imm rs ss is_v1 pc fm enable_stack_frame_gaps
                program_vm_addr
              with None -> BPF_EFlag
              | Some (pca, (rsa, ssa)) ->
                BPF_OK (pca, rsa, m, ssa, sv, fm, cur_cu, remain_cu))
          | BPF_CALL_IMM (src, imm) ->
            (match
              eval_call_imm pc src imm rs ss is_v1 fm enable_stack_frame_gaps
              with None -> BPF_EFlag
              | Some (pca, (rsa, ssa)) ->
                BPF_OK (pca, rsa, m, ssa, sv, fm, cur_cu, remain_cu))
          | BPF_EXIT ->
            (if equal_word
                  (len_bit0
                    (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                  (call_depth ss)
                  (zero_word
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
              then (if less_word
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         remain_cu cur_cu
                     then BPF_EFlag else BPF_Success (rs BR0))
              else (let (pca, (rsa, ssa)) = eval_exit rs ss is_v1 in
                     BPF_OK (pca, rsa, m, ssa, sv, fm, cur_cu, remain_cu)))));;

let rec init_func_map x = (fun _ -> None) x;;

let rec intlist_to_reg_map
  l = (fun a ->
        (match a
          with BR0 ->
            of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nth l Zero_nat)
          | BR1 ->
            of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nth l one_nat)
          | BR2 ->
            of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nth l (nat_of_num (Bit0 One)))
          | BR3 ->
            of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nth l (nat_of_num (Bit1 One)))
          | BR4 ->
            of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nth l (nat_of_num (Bit0 (Bit0 One))))
          | BR5 ->
            of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nth l (nat_of_num (Bit1 (Bit0 One))))
          | BR6 ->
            of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nth l (nat_of_num (Bit0 (Bit1 One))))
          | BR7 ->
            of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nth l (nat_of_num (Bit1 (Bit1 One))))
          | BR8 ->
            of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nth l (nat_of_num (Bit0 (Bit0 (Bit0 One)))))
          | BR9 ->
            of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nth l (nat_of_num (Bit1 (Bit0 (Bit0 One)))))
          | BR10 ->
            of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (nth l (nat_of_num (Bit0 (Bit1 (Bit0 One)))))));;

let rec create_list x0 uu = match x0, uu with Zero_nat, uu -> []
                      | Suc n, def_v -> [def_v] @ create_list n def_v;;

let init_stack_state : unit stack_state_ext
  = Stack_state_ext
      (zero_word
         (len_bit0
           (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
        plus_word
          (len_bit0
            (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
          (of_int
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
   (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
     (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
   (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))))))))))))))))))))))))))))
          (times_worda
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
     (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))))))
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))),
        create_list
          (the_nat
            (len_bit0
              (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
            (of_int
              (len_bit0
                (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
              (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
          (CallFrame_ext
            ([], zero_word
                   (len_bit0
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
              zero_word
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))),
              ())),
        ());;

let rec int_to_bpf_ireg
  i = (match u4_to_bpf_ireg (of_int (len_bit0 (len_bit0 len_num1)) i)
        with None -> BR0 | Some v -> v);;

let rec unsigned_bitfield_extract_u8
  pos width n =
    and_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
      (minus_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (power (power_word (len_bit0 (len_bit0 (len_bit0 len_num1))))
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit0 One)))
          width)
        (one_worda (len_bit0 (len_bit0 (len_bit0 len_num1)))))
      (drop_bit_word (len_bit0 (len_bit0 (len_bit0 len_num1))) pos n);;

let rec rbpf_decoder
  opc dv sv off imm =
    (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
            (Pos (Bit1 (Bit1 One))))
      then (if equal_word (len_bit0 (len_bit0 len_num1)) dv
                 (of_int (len_bit0 (len_bit0 len_num1))
                   (Pos (Bit1 (Bit1 (Bit0 One)))))
             then Some (BPF_ADD_STK imm)
             else (match u4_to_bpf_ireg dv with None -> None
                    | Some dst -> Some (BPF_ALU64 (BPF_ADD, dst, SOImm imm))))
      else (match u4_to_bpf_ireg dv with None -> None
             | Some dst ->
               (match u4_to_bpf_ireg sv with None -> None
                 | Some src ->
                   (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           (Pos (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One))))))))
                     then Some (BPF_LDX (M8, dst, src, off))
                     else (if equal_word
                                (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit1
 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One))))))))
                            then Some (BPF_LDX (M16, dst, src, off))
                            else (if equal_word
                                       (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                       opc (of_int
     (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))))))
                                   then Some (BPF_LDX (M32, dst, src, off))
                                   else (if equal_word
      (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (Pos (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
  then Some (BPF_LDX (M64, dst, src, off))
  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
             (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
               (Pos (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One))))))))
         then Some (BPF_ST (M8, dst, SOImm imm, off))
         else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                      (Pos (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One))))))))
                then Some (BPF_ST (M16, dst, SOImm imm, off))
                else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           opc (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit0
(Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One))))))))
                       then Some (BPF_ST (M32, dst, SOImm imm, off))
                       else (if equal_word
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                  (of_int
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    (Pos (Bit0
   (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
                              then Some (BPF_ST (M64, dst, SOImm imm, off))
                              else (if equal_word
 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
   (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One))))))))
                                     then Some (BPF_ST
         (M8, dst, SOReg src, off))
                                     else (if equal_word
        (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One))))))))
    then Some (BPF_ST (M16, dst, SOReg src, off))
    else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One))))))))
           then Some (BPF_ST (M32, dst, SOReg src, off))
           else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (Pos (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
                  then Some (BPF_ST (M64, dst, SOReg src, off))
                  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                             opc (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit0 (Bit0 One))))
                         then Some (BPF_ALU (BPF_ADD, dst, SOImm imm))
                         else (if equal_word
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    opc (of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit0 (Bit0 (Bit1 One)))))
                                then Some (BPF_ALU (BPF_ADD, dst, SOReg src))
                                else (if equal_word
   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit0 (Bit0 (Bit1 (Bit0 One))))))
                                       then Some (BPF_ALU
           (BPF_SUB, dst, SOImm imm))
                                       else (if equal_word
          (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
            (Pos (Bit0 (Bit0 (Bit1 (Bit1 One))))))
      then Some (BPF_ALU (BPF_SUB, dst, SOReg src))
      else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
             then Some (BPF_ALU (BPF_MUL, dst, SOImm imm))
             else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
                    then Some (BPF_ALU (BPF_MUL, dst, SOReg src))
                    else (if equal_word
                               (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
                           then Some (BPF_ALU (BPF_DIV, dst, SOImm imm))
                           else (if equal_word
                                      (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                      opc (of_int
    (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
                                  then Some (BPF_ALU (BPF_DIV, dst, SOReg src))
                                  else (if equal_word
     (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
       (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))))
 then Some (BPF_ALU (BPF_OR, dst, SOImm imm))
 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
            (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
              (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One))))))))
        then Some (BPF_ALU (BPF_OR, dst, SOReg src))
        else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                     (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One))))))))
               then Some (BPF_ALU (BPF_AND, dst, SOImm imm))
               else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One))))))))
                      then Some (BPF_ALU (BPF_AND, dst, SOReg src))
                      else (if equal_word
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                 (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit0
  (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One))))))))
                             then Some (BPF_ALU (BPF_LSH, dst, SOImm imm))
                             else (if equal_word
(len_bit0 (len_bit0 (len_bit0 len_num1))) opc
(of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One))))))))
                                    then Some (BPF_ALU
        (BPF_LSH, dst, SOReg src))
                                    else (if equal_word
       (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
       (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One))))))))
   then Some (BPF_ALU (BPF_RSH, dst, SOImm imm))
   else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
              (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))
          then Some (BPF_ALU (BPF_RSH, dst, SOReg src))
          else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                       (Pos (Bit0 (Bit0 (Bit1
  (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
                 then Some (BPF_NEG32_REG dst)
                 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            opc (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit0
 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))))
                        then Some (BPF_ALU (BPF_MOD, dst, SOImm imm))
                        else (if equal_word
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                   (of_int
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     (Pos (Bit0
    (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))))
                               then Some (BPF_ALU (BPF_MOD, dst, SOReg src))
                               else (if equal_word
  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
  (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))))
                                      then Some (BPF_ALU
          (BPF_XOR, dst, SOImm imm))
                                      else (if equal_word
         (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
           (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))))
     then Some (BPF_ALU (BPF_XOR, dst, SOReg src))
     else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                  (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))))
            then Some (BPF_ALU (BPF_MOV, dst, SOImm imm))
            else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                       (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                         (Pos (Bit0 (Bit0 (Bit1
    (Bit1 (Bit1 (Bit1 (Bit0 One)))))))))
                   then Some (BPF_ALU (BPF_MOV, dst, SOReg src))
                   else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                              opc (of_int
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    (Pos (Bit0
   (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))))
                          then Some (BPF_ALU (BPF_ARSH, dst, SOImm imm))
                          else (if equal_word
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     opc (of_int
   (len_bit0 (len_bit0 (len_bit0 len_num1)))
   (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))))
                                 then Some (BPF_ALU (BPF_ARSH, dst, SOReg src))
                                 else (if equal_word
    (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
      (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))))
then Some (BPF_LE (dst, imm))
else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
           (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
             (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))))
       then Some (BPF_BE (dst, imm))
       else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                  (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                    (Pos (Bit1 (Bit1 (Bit1 One)))))
              then Some (BPF_ALU64 (BPF_ADD, dst, SOReg src))
              else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           (Pos (Bit1 (Bit1 (Bit1 (Bit0 One))))))
                     then Some (BPF_ALU64 (BPF_SUB, dst, SOImm imm))
                     else (if equal_word
                                (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit1 (Bit1 (Bit1 (Bit1 One))))))
                            then Some (BPF_ALU64 (BPF_SUB, dst, SOReg src))
                            else (if equal_word
                                       (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                       opc (of_int
     (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))
                                   then Some (BPF_ALU64
       (BPF_MUL, dst, SOImm imm))
                                   else (if equal_word
      (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))
  then Some (BPF_ALU64 (BPF_MUL, dst, SOReg src))
  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
             (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
               (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
         then Some (BPF_ALU64 (BPF_DIV, dst, SOImm imm))
         else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                      (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
                then Some (BPF_ALU64 (BPF_DIV, dst, SOReg src))
                else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           opc (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit1
(Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One))))))))
                       then Some (BPF_ALU64 (BPF_OR, dst, SOImm imm))
                       else (if equal_word
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                  (of_int
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    (Pos (Bit1
   (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One))))))))
                              then Some (BPF_ALU64 (BPF_OR, dst, SOReg src))
                              else (if equal_word
 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
   (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One))))))))
                                     then Some (BPF_ALU64
         (BPF_AND, dst, SOImm imm))
                                     else (if equal_word
        (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One))))))))
    then Some (BPF_ALU64 (BPF_AND, dst, SOReg src))
    else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One))))))))
           then Some (BPF_ALU64 (BPF_LSH, dst, SOImm imm))
           else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One))))))))
                  then Some (BPF_ALU64 (BPF_LSH, dst, SOReg src))
                  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                             opc (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit1
  (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One))))))))
                         then Some (BPF_ALU64 (BPF_RSH, dst, SOImm imm))
                         else (if equal_word
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    opc (of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))
                                then Some (BPF_ALU64 (BPF_RSH, dst, SOReg src))
                                else (if equal_word
   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
                                       then Some (BPF_NEG64_REG dst)
                                       else (if equal_word
          (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
            (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))))
      then Some (BPF_ALU64 (BPF_MOD, dst, SOImm imm))
      else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))))
             then Some (BPF_ALU64 (BPF_MOD, dst, SOReg src))
             else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (Pos (Bit1 (Bit1 (Bit1
     (Bit0 (Bit0 (Bit1 (Bit0 One)))))))))
                    then Some (BPF_ALU64 (BPF_XOR, dst, SOImm imm))
                    else (if equal_word
                               (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit1
(Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))))
                           then Some (BPF_ALU64 (BPF_XOR, dst, SOReg src))
                           else (if equal_word
                                      (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                      opc (of_int
    (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))))
                                  then Some (BPF_ALU64
      (BPF_MOV, dst, SOImm imm))
                                  else (if equal_word
     (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
       (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))))
 then Some (BPF_ALU64 (BPF_MOV, dst, SOReg src))
 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
            (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
              (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))))
        then Some (BPF_ALU64 (BPF_ARSH, dst, SOImm imm))
        else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                     (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))))
               then Some (BPF_ALU64 (BPF_ARSH, dst, SOReg src))
               else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit1 (Bit1
 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))))
                      then Some (BPF_HOR64_IMM (dst, imm))
                      else (if equal_word
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                 (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit0
  (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
                             then Some (BPF_PQR (BPF_LMUL, dst, SOImm imm))
                             else (if equal_word
(len_bit0 (len_bit0 (len_bit0 len_num1))) opc
(of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))))
                                    then Some (BPF_PQR
        (BPF_LMUL, dst, SOReg src))
                                    else (if equal_word
       (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
       (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))))
   then Some (BPF_PQR64 (BPF_LMUL, dst, SOImm imm))
   else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
              (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))))
          then Some (BPF_PQR64 (BPF_LMUL, dst, SOReg src))
          else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                       (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
                 then Some (BPF_PQR2 (BPF_UHMUL, dst, SOImm imm))
                 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            opc (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
                        then Some (BPF_PQR2 (BPF_UHMUL, dst, SOReg src))
                        else (if equal_word
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                   (of_int
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     (Pos (Bit0
    (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))))
                               then Some (BPF_PQR2 (BPF_SHMUL, dst, SOImm imm))
                               else (if equal_word
  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
  (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))))
                                      then Some (BPF_PQR2
          (BPF_SHMUL, dst, SOReg src))
                                      else (if equal_word
         (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
           (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One))))))))
     then Some (BPF_PQR (BPF_UDIV, dst, SOImm imm))
     else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                  (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One))))))))
            then Some (BPF_PQR (BPF_UDIV, dst, SOReg src))
            else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                       (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                         (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One))))))))
                   then Some (BPF_PQR64 (BPF_UDIV, dst, SOImm imm))
                   else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                              opc (of_int
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    (Pos (Bit0
   (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One))))))))
                          then Some (BPF_PQR64 (BPF_UDIV, dst, SOReg src))
                          else (if equal_word
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     opc (of_int
   (len_bit0 (len_bit0 (len_bit0 len_num1)))
   (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One))))))))
                                 then Some (BPF_PQR (BPF_UREM, dst, SOImm imm))
                                 else (if equal_word
    (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
      (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One))))))))
then Some (BPF_PQR (BPF_UREM, dst, SOReg src))
else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
           (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
             (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One))))))))
       then Some (BPF_PQR64 (BPF_UREM, dst, SOImm imm))
       else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                  (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                    (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))
              then Some (BPF_PQR64 (BPF_UREM, dst, SOReg src))
              else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           (Pos (Bit0 (Bit1
(Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))))
                     then Some (BPF_PQR (BPF_SDIV, dst, SOImm imm))
                     else (if equal_word
                                (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit0
 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))))
                            then Some (BPF_PQR (BPF_SDIV, dst, SOReg src))
                            else (if equal_word
                                       (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                       opc (of_int
     (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))))
                                   then Some (BPF_PQR64
       (BPF_SDIV, dst, SOImm imm))
                                   else (if equal_word
      (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))))
  then Some (BPF_PQR64 (BPF_SDIV, dst, SOReg src))
  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
             (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
               (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))))))))
         then Some (BPF_PQR (BPF_SREM, dst, SOImm imm))
         else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                    (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                      (Pos (Bit0 (Bit1 (Bit1
 (Bit1 (Bit0 (Bit1 (Bit1 One)))))))))
                then Some (BPF_PQR (BPF_SREM, dst, SOReg src))
                else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           opc (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit0
(Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))))
                       then Some (BPF_PQR64 (BPF_SREM, dst, SOImm imm))
                       else (if equal_word
                                  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                  (of_int
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    (Pos (Bit0
   (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))))
                              then Some (BPF_PQR64 (BPF_SREM, dst, SOReg src))
                              else (if equal_word
 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1))) (Pos (Bit1 (Bit0 One))))
                                     then Some (BPF_JA off)
                                     else (if equal_word
        (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (Pos (Bit1 (Bit0 (Bit1 (Bit0 One))))))
    then Some (BPF_JUMP (Eq, dst, SOImm imm, off))
    else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                 (Pos (Bit1 (Bit0 (Bit1 (Bit1 One))))))
           then Some (BPF_JUMP (Eq, dst, SOReg src, off))
           else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
                  then Some (BPF_JUMP (Gt, dst, SOImm imm, off))
                  else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                             opc (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
                         then Some (BPF_JUMP (Gt, dst, SOReg src, off))
                         else (if equal_word
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                    opc (of_int
  (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
                                then Some (BPF_JUMP (Ge, dst, SOImm imm, off))
                                else (if equal_word
   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
     (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
                                       then Some (BPF_JUMP
           (Ge, dst, SOReg src, off))
                                       else (if equal_word
          (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
            (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))))
      then Some (BPF_JUMP (Lt, dst, SOImm imm, off))
      else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                 (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                   (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))))
             then Some (BPF_JUMP (Lt, dst, SOReg src, off))
             else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                        (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                          (Pos (Bit1 (Bit0 (Bit1
     (Bit0 (Bit1 (Bit1 (Bit0 One)))))))))
                    then Some (BPF_JUMP (Le, dst, SOImm imm, off))
                    else (if equal_word
                               (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                               (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                 (Pos (Bit1
(Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))))
                           then Some (BPF_JUMP (Le, dst, SOReg src, off))
                           else (if equal_word
                                      (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                      opc (of_int
    (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))))
                                  then Some (BPF_JUMP
      (SEt, dst, SOImm imm, off))
                                  else (if equal_word
     (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
       (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One))))))))
 then Some (BPF_JUMP (SEt, dst, SOReg src, off))
 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
            (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
              (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One))))))))
        then Some (BPF_JUMP (Ne, dst, SOImm imm, off))
        else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                   (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                     (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One))))))))
               then Some (BPF_JUMP (Ne, dst, SOReg src, off))
               else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                          (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One))))))))
                      then Some (BPF_JUMP (SGt, dst, SOImm imm, off))
                      else (if equal_word
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                 (of_int
                                   (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (Pos (Bit1
  (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One))))))))
                             then Some (BPF_JUMP (SGt, dst, SOReg src, off))
                             else (if equal_word
(len_bit0 (len_bit0 (len_bit0 len_num1))) opc
(of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
  (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One))))))))
                                    then Some (BPF_JUMP
        (SGe, dst, SOImm imm, off))
                                    else (if equal_word
       (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
       (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
         (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))
   then Some (BPF_JUMP (SGe, dst, SOReg src, off))
   else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
              (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))))
          then Some (BPF_JUMP (SLt, dst, SOImm imm, off))
          else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                     (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                       (Pos (Bit1 (Bit0 (Bit1
  (Bit1 (Bit0 (Bit0 (Bit1 One)))))))))
                 then Some (BPF_JUMP (SLt, dst, SOReg src, off))
                 else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1)))
                            opc (of_int
                                  (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                  (Pos (Bit1
 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))))
                        then Some (BPF_JUMP (SLe, dst, SOImm imm, off))
                        else (if equal_word
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                                   (of_int
                                     (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                     (Pos (Bit1
    (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))))
                               then Some (BPF_JUMP (SLe, dst, SOReg src, off))
                               else (if equal_word
  (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
  (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (Pos (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))))
                                      then Some (BPF_CALL_REG (src, imm))
                                      else (if equal_word
         (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
         (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
           (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
     then Some (BPF_CALL_IMM (src, imm))
     else (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) opc
                (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                  (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))))
            then Some BPF_EXIT
            else None)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));;

let rec bpf_find_instr
  pc l =
    (let npc = times_nat pc iNSN_SIZE in
     let op = nth l npc in
     let reg = nth l (plus_nat npc one_nat) in
     let dst =
       unsigned_bitfield_extract_u8 Zero_nat (nat_of_num (Bit0 (Bit0 One))) reg
       in
     let src =
       unsigned_bitfield_extract_u8 (nat_of_num (Bit0 (Bit0 One)))
         (nat_of_num (Bit0 (Bit0 One))) reg
       in
      (match
        u16_of_u8_list
          [nth l (plus_nat npc (nat_of_num (Bit0 One)));
            nth l (plus_nat npc (nat_of_num (Bit1 One)))]
        with None -> None
        | Some off_v ->
          (match
            u32_of_u8_list
              [nth l (plus_nat npc (nat_of_num (Bit0 (Bit0 One))));
                nth l (plus_nat npc (nat_of_num (Bit1 (Bit0 One))));
                nth l (plus_nat npc (nat_of_num (Bit0 (Bit1 One))));
                nth l (plus_nat npc (nat_of_num (Bit1 (Bit1 One))))]
            with None -> None
            | Some i1 ->
              (let off =
                 signed_cast
                   (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
                   (len_signed
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                   off_v
                 in
               let imm =
                 signed_cast
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                   (len_signed
                     (len_bit0
                       (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                   i1
                 in
                (if equal_word (len_bit0 (len_bit0 (len_bit0 len_num1))) op
                      (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))
                        (Pos (Bit0 (Bit0 (Bit0 (Bit1 One))))))
                  then (match
                         u32_of_u8_list
                           [nth l (plus_nat npc
                                    (nat_of_num (Bit0 (Bit0 (Bit1 One)))));
                             nth l (plus_nat npc
                                     (nat_of_num (Bit1 (Bit0 (Bit1 One)))));
                             nth l (plus_nat npc
                                     (nat_of_num (Bit0 (Bit1 (Bit1 One)))));
                             nth l (plus_nat npc
                                     (nat_of_num (Bit1 (Bit1 (Bit1 One)))))]
                         with None -> None
                         | Some i2 ->
                           (let imm2 =
                              signed_cast
                                (len_bit0
                                  (len_bit0
                                    (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                                (len_signed
                                  (len_bit0
                                    (len_bit0
                                      (len_bit0
(len_bit0 (len_bit0 len_num1))))))
                                i2
                              in
                             (match
                               u4_to_bpf_ireg
                                 (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                                   (len_bit0 (len_bit0 len_num1)) dst)
                               with None -> None
                               | Some dst_r ->
                                 Some (BPF_LD_IMM (dst_r, imm, imm2)))))
                  else rbpf_decoder op
                         (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           (len_bit0 (len_bit0 len_num1)) dst)
                         (cast (len_bit0 (len_bit0 (len_bit0 len_num1)))
                           (len_bit0 (len_bit0 len_num1)) src)
                         off imm)))));;

let rec less_nat m x1 = match m, x1 with m, Suc n -> less_eq_nat m n
                   | n, Zero_nat -> false
and less_eq_nat x0 n = match x0, n with Suc m, n -> less_nat m n
                  | Zero_nat, n -> true;;


let rec num_to_int (n: num) : int64 =
  match n with
  | One -> 1L
  | Bit0 m -> Int64.mul 2L (num_to_int m)
  | Bit1 m -> Int64.add (Int64.mul 2L (num_to_int m)) 1L     

let myint_to_int (mi: myint) : int64 =
  match mi with
  | Zero_int -> 0L
  | Pos n -> num_to_int n
  | Neg n -> Int64.neg (num_to_int n)

let rec num_of_int (n: int64) =
  if n = 1L then One
  else if Int64.rem n 2L = 0L then Bit0 (num_of_int (Int64.div n 2L))
  else Bit1 (num_of_int (Int64.div n 2L))


let int_of_standard_int (n: int64) =
  if n = 0L then Zero_int
  else if n > 0L then  Pos (num_of_int (n))
  else Neg (num_of_int (Int64.sub 0L n))

let int_list_of_standard_int_list lst =
  List.map int_of_standard_int lst

let print_regmap rs =
  let reg_list = [("R0", BR0); ("R1", BR1); ("R2", BR2); ("R3", BR3);
                  ("R4", BR4); ("R5", BR5); ("R6", BR6); ("R7", BR7);
                  ("R8", BR8); ("R9", BR9); ("R10", BR10)] in
  List.iter (fun (name, reg) ->
    Printf.printf "%s: %Lx\n" name (myint_to_int (the_int
    (len_bit0
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        (rs reg)))
  ) reg_list

let print_bpf_state st =
  match st with
    BPF_OK (pc, rs, m, ss, sv, fm, cur_cu, remain_cu) -> 
    let _ = print_regmap rs in
      Printf.printf "PC: %Lx\n" (myint_to_int (the_int
    (len_bit0
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        pc))
  | BPF_Success _ -> print_endline("success")
  | _ -> print_endline("error")

let rec u8_list_to_mem
  l = (fun i ->
        (if less_nat
              (the_nat
                (len_bit0
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                i)
              (size_list l)
          then Some (nth l
                      (the_nat
                        (len_bit0
                          (len_bit0
                            (len_bit0
                              (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                        i))
          else None));;

let rec int_to_u8_list
  lp = map (of_int (len_bit0 (len_bit0 (len_bit0 len_num1)))) lp;;

let rec step_test
  lp lr lm lc v fuel ipc i res =
    (let prog = int_to_u8_list lp in
     let rs =
       fun_upd equal_bpf_ireg (intlist_to_reg_map lr) BR10
         (plus_word
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
           (of_int
             (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
    (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
  (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
(Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
    (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))))))))))))))))))))))))))))
           (times_worda
             (len_bit0
               (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
             (of_int
               (len_bit0
                 (len_bit0
                   (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               (Pos (Bit0 (Bit0 (Bit0 (Bit0
(Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))))))
             (of_int
               (len_bit0
                 (len_bit0
                   (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
               (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))
       in
     let m = u8_list_to_mem (int_to_u8_list lm) in
     let stk = init_stack_state in
     let sv = (if equal_int v one_inta then V1 else V2) in
     let fm = init_func_map in 
      (match bpf_find_instr Zero_nat prog with None -> false
        | Some ins0 ->
          (let st1 =
             step (zero_word
                    (len_bit0
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
               ins0 rs m stk sv fm true
               (of_int
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 (Pos (Bit0 (Bit0 (Bit0 (Bit0
  (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
(Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
    (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
  (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))))))))))))))))))))))))))
               (zero_word
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
               (of_int
                 (len_bit0
                   (len_bit0
                     (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                 (Pos (Bit1 One)))
             in
            let _ = print_bpf_state st1 in
            (if equal_nat (size_list lp) (nat_of_num (Bit0 (Bit0 (Bit0 One))))
              then (match st1
                     with BPF_OK (pc1, rs1, _, _, _, _, _, _) ->
                       equal_word
                         (len_bit0
                           (len_bit0
                             (len_bit0
                               (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                         pc1 (of_int
                               (len_bit0
                                 (len_bit0
                                   (len_bit0
                                     (len_bit0
                                       (len_bit0 (len_bit0 len_num1))))))
                               ipc) &&
                         equal_word
                           (len_bit0
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                           (rs1 (int_to_bpf_ireg i))
                           (of_int
                             (len_bit0
                               (len_bit0
                                 (len_bit0
                                   (len_bit0 (len_bit0 (len_bit0 len_num1))))))
                             res)
                     | BPF_Success _ -> false | BPF_EFlag -> false
                     | BPF_Err -> false)
              else (if equal_nat (size_list lp)
                         (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One)))))
                     then (match st1
                            with BPF_OK (pc1, rs1, m1, ss1, sv1, fm1, _, _) ->
                              (match bpf_find_instr one_nat prog
                                with None -> false
                                | Some ins1 ->
                                  (match
                                    step pc1 ins1 rs1 m1 ss1 sv1 fm1 true
                                      (of_int
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
(Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
   (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
     (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0
   (Bit0 (Bit0 (Bit0 One))))))))))))))))))))))))))))))))))
                                      (one_worda
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))))
                                      (of_int
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
(Pos (Bit0 One)))
                                    with BPF_OK (pc2, rs2, _, _, _, _, _, _) ->
                                      equal_word
(len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))) pc2
(of_int
  (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
  ipc) &&
equal_word
  (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
  (rs2 (int_to_bpf_ireg i))
  (of_int
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
    res)
                                    | BPF_Success _ -> false
                                    | BPF_EFlag -> false | BPF_Err -> false))
                            | BPF_Success _ -> false | BPF_EFlag -> false
                            | BPF_Err -> false)
                     else false)))));;

end;; (*struct Step_test*)
