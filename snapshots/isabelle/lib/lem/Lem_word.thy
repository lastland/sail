chapter \<open>Generated by Lem from word.lem.\<close>

theory "Lem_word" 

imports 
 	 Main
	 "Lem_bool" 
	 "Lem_maybe" 
	 "Lem_num" 
	 "Lem_basic_classes" 
	 "Lem_list" 
	 "~~/src/HOL/Word/Word" 

begin 



(*open import Bool Maybe Num Basic_classes List*)

(*open import {isabelle} `~~/src/HOL/Word/Word`*)
(*open import {hol} `wordsTheory` `wordsLib`*)


(* ========================================================================== *)
(* Define general purpose word, i.e. sequences of bits of arbitrary length    *)
(* ========================================================================== *)

datatype bitSequence = BitSeq " 
    nat option  " " (* length of the sequence, Nothing means infinite length *)
   bool " " bool       (* sign of the word, used to fill up after concrete value is exhausted *)
   list "    (* the initial part of the sequence, least significant bit first *)

(*val bitSeqEq : bitSequence -> bitSequence -> bool*)

(*val boolListFrombitSeq : nat -> bitSequence -> list bool*)

fun  boolListFrombitSeqAux  :: " nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list "  where 
     " boolListFrombitSeqAux n s bl = (
  if n =( 0 :: nat) then [] else
  (case  bl of
      []       => List.replicate n s
    | b # bl' => b # (boolListFrombitSeqAux (n-( 1 :: nat)) s bl')
  ))"


fun boolListFrombitSeq  :: " nat \<Rightarrow> bitSequence \<Rightarrow>(bool)list "  where 
     " boolListFrombitSeq n (BitSeq _ s bl) = ( boolListFrombitSeqAux n s bl )"



(*val bitSeqFromBoolList : list bool -> maybe bitSequence*)
definition bitSeqFromBoolList  :: "(bool)list \<Rightarrow>(bitSequence)option "  where 
     " bitSeqFromBoolList bl = (
  (case  dest_init bl of
      None => None
    | Some (bl', s) => Some (BitSeq (Some (List.length bl)) s bl')
  ))"



(* cleans up the representation of a bitSequence without changing its semantics *)
(*val cleanBitSeq : bitSequence -> bitSequence*)
fun cleanBitSeq  :: " bitSequence \<Rightarrow> bitSequence "  where 
     " cleanBitSeq (BitSeq len s bl) = ( (case  len of
    None => (BitSeq len s (List.rev (dropWhile ((op \<longleftrightarrow>) s) (List.rev bl))))
  | Some n  => (BitSeq len s (List.rev (dropWhile ((op \<longleftrightarrow>) s) (List.rev (List.take (n-( 1 :: nat)) bl)))))
))"



(*val bitSeqTestBit : bitSequence -> nat -> maybe bool*)
fun bitSeqTestBit  :: " bitSequence \<Rightarrow> nat \<Rightarrow>(bool)option "  where 
     " bitSeqTestBit (BitSeq None s bl) pos = ( if pos < List.length bl then index bl pos else Some s )"
|" bitSeqTestBit (BitSeq(Some l) s bl) pos = ( if (pos \<ge> l) then None else
                if ((pos = (l -( 1 :: nat))) \<or> (pos \<ge> List.length bl)) then Some s else
                index bl pos )"


(*val bitSeqSetBit : bitSequence -> nat -> bool -> bitSequence*)
fun bitSeqSetBit  :: " bitSequence \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bitSequence "  where 
     " bitSeqSetBit (BitSeq len s bl) pos v = (
  (let bl' = (if (pos < List.length bl) then bl else bl @ List.replicate pos s) in
  (let bl'' = (List.list_update bl' pos v) in
  (let bs' = (BitSeq len s bl'') in
  cleanBitSeq bs'))))"



(*val resizeBitSeq : maybe nat -> bitSequence -> bitSequence*)
definition resizeBitSeq  :: "(nat)option \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " resizeBitSeq new_len bs = ( 
  (case  cleanBitSeq bs of
      (BitSeq len s bl) =>
  (let shorten_opt = ((case  (new_len, len) of
                            (None, _) => None
                        | (Some l1, None) => Some l1
                        | (Some l1, Some l2) =>
                      if (l1 < l2) then Some l1 else None
                      )) in
  (case  shorten_opt of
        None => BitSeq new_len s bl
    | Some l1 => (
                 (let bl' = (List.take l1 (bl @ [s])) in
                 (case  dest_init bl' of
                       None => (BitSeq len s bl) (* do nothing if size 0 is requested *)
                   | Some (bl'', s') => cleanBitSeq (BitSeq new_len s' bl'')
                 )))
  ))
  ) )"
 

(*val bitSeqNot : bitSequence -> bitSequence*)
fun bitSeqNot  :: " bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqNot (BitSeq len s bl) = ( BitSeq len (\<not> s) (List.map (\<lambda> x. \<not> x) bl))"


(*val bitSeqBinop : (bool -> bool -> bool) -> bitSequence -> bitSequence -> bitSequence*)

(*val bitSeqBinopAux : (bool -> bool -> bool) -> bool -> list bool -> bool -> list bool -> list bool*)
fun  bitSeqBinopAux  :: "(bool \<Rightarrow> bool \<Rightarrow> bool)\<Rightarrow> bool \<Rightarrow>(bool)list \<Rightarrow> bool \<Rightarrow>(bool)list \<Rightarrow>(bool)list "  where 
     " bitSeqBinopAux binop s1 ([]) s2 ([]) = ( [])"
|" bitSeqBinopAux binop s1 (b1 # bl1') s2 ([]) = ( (binop b1 s2) # bitSeqBinopAux binop s1 bl1' s2 [])"
|" bitSeqBinopAux binop s1 ([]) s2 (b2 # bl2') = ( (binop s1 b2) # bitSeqBinopAux binop s1 []   s2 bl2' )"
|" bitSeqBinopAux binop s1 (b1 # bl1') s2 (b2 # bl2') = ( (binop b1 b2) # bitSeqBinopAux binop s1 bl1' s2 bl2' )"


definition bitSeqBinop  :: "(bool \<Rightarrow> bool \<Rightarrow> bool)\<Rightarrow> bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqBinop binop bs1 bs2 = ( ( 
  (case  cleanBitSeq bs1 of
      (BitSeq len1 s1 bl1) =>
  (case  cleanBitSeq bs2 of
      (BitSeq len2 s2 bl2) =>
  (let len = ((case  (len1, len2) of
                    (Some l1, Some l2) => Some (max l1 l2)
                | _ => None
              )) in
  (let s = (binop s1 s2) in
  (let bl = (bitSeqBinopAux binop s1 bl1 s2 bl2) in
  cleanBitSeq (BitSeq len s bl))))
  )
  )
))"


definition bitSeqAnd  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqAnd = ( bitSeqBinop (op \<and>))"

definition bitSeqOr  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqOr = ( bitSeqBinop (op \<or>))"

definition bitSeqXor  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqXor = ( bitSeqBinop (\<lambda> b1 b2. \<not> (b1 \<longleftrightarrow> b2)))"


(*val bitSeqShiftLeft : bitSequence -> nat -> bitSequence*)
fun bitSeqShiftLeft  :: " bitSequence \<Rightarrow> nat \<Rightarrow> bitSequence "  where 
     " bitSeqShiftLeft (BitSeq len s bl) n = ( cleanBitSeq (BitSeq len s (List.replicate n False @ bl)))"


(*val bitSeqArithmeticShiftRight : bitSequence -> nat -> bitSequence*)
definition bitSeqArithmeticShiftRight  :: " bitSequence \<Rightarrow> nat \<Rightarrow> bitSequence "  where 
     " bitSeqArithmeticShiftRight bs n = ( 
  (case  cleanBitSeq bs of
      (BitSeq len s bl) =>
  cleanBitSeq (BitSeq len s (List.drop n bl))
  ) )"


(*val bitSeqLogicalShiftRight : bitSequence -> nat -> bitSequence*)
definition bitSeqLogicalShiftRight  :: " bitSequence \<Rightarrow> nat \<Rightarrow> bitSequence "  where 
     " bitSeqLogicalShiftRight bs n = ( 
  if (n =( 0 :: nat)) then cleanBitSeq bs else  
  (case  cleanBitSeq bs of
      (BitSeq len s bl) =>
  (case  len of
        None => cleanBitSeq (BitSeq len s (List.drop n bl))
    | Some l => cleanBitSeq
                  (BitSeq len False ((List.drop n bl) @ List.replicate l s))
  )
  ) )"



(* integerFromBoolList sign bl creates an integer from a list of bits
   (least significant bit first) and an explicitly given sign bit.
   It uses two's complement encoding. *)
(*val integerFromBoolList : (bool * list bool) -> integer*)

fun  integerFromBoolListAux  :: " int \<Rightarrow>(bool)list \<Rightarrow> int "  where 
     " integerFromBoolListAux (acc1 :: int) (([]) :: bool list) = ( acc1 )"
|" integerFromBoolListAux (acc1 :: int) ((True # bl') :: bool list) = ( integerFromBoolListAux ((acc1 *( 2 :: int)) +( 1 :: int)) bl' )"
|" integerFromBoolListAux (acc1 :: int) ((False # bl') :: bool list) = ( integerFromBoolListAux (acc1 *( 2 :: int)) bl' )"


fun integerFromBoolList  :: " bool*(bool)list \<Rightarrow> int "  where 
     " integerFromBoolList (sign, bl) = ( 
   if sign then 
     - (integerFromBoolListAux(( 0 :: int)) (List.rev (List.map (\<lambda> x. \<not> x) bl)) +( 1 :: int))
   else integerFromBoolListAux(( 0 :: int)) (List.rev bl))"


(* [boolListFromInteger i] creates a sign bit and a list of booleans from an integer. The len_opt tells it when to stop.*)
(*val boolListFromInteger :    integer -> bool * list bool*)

fun  boolListFromNatural  :: "(bool)list \<Rightarrow> nat \<Rightarrow>(bool)list "  where 
     " boolListFromNatural acc1 (remainder :: nat) = (
 if (remainder >( 0 :: nat)) then 
   (boolListFromNatural (((remainder mod( 2 :: nat)) =( 1 :: nat)) # acc1) 
      (remainder div( 2 :: nat)))
 else
   List.rev acc1 )"


definition boolListFromInteger  :: " int \<Rightarrow> bool*(bool)list "  where 
     " boolListFromInteger (i :: int) = ( 
  if (i <( 0 :: int)) then
    (True, List.map (\<lambda> x. \<not> x) (boolListFromNatural [] (nat (abs (- (i +( 1 :: int)))))))
  else
    (False, boolListFromNatural [] (nat (abs i))))"



(* [bitSeqFromInteger len_opt i] encodes [i] as a bitsequence with [len_opt] bits. If there are not enough
   bits, truncation happens *)
(*val bitSeqFromInteger : maybe nat -> integer -> bitSequence*)
definition bitSeqFromInteger  :: "(nat)option \<Rightarrow> int \<Rightarrow> bitSequence "  where 
     " bitSeqFromInteger len_opt i = (
  (let (s, bl) = (boolListFromInteger i) in
  resizeBitSeq len_opt (BitSeq None s bl)))"



(*val integerFromBitSeq : bitSequence -> integer*)
definition integerFromBitSeq  :: " bitSequence \<Rightarrow> int "  where 
     " integerFromBitSeq bs = ( 
  (case  cleanBitSeq bs of (BitSeq len s bl) => integerFromBoolList (s, bl) ) )"



(* Now we can via translation to integers map arithmetic operations to bitSequences *)

(*val bitSeqArithUnaryOp : (integer -> integer) -> bitSequence -> bitSequence*)
definition bitSeqArithUnaryOp  :: "(int \<Rightarrow> int)\<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqArithUnaryOp uop bs = ( 
  (case  bs of
      (BitSeq len _ _) =>
  bitSeqFromInteger len (uop (integerFromBitSeq bs))
  ) )"


(*val bitSeqArithBinOp : (integer -> integer -> integer) -> bitSequence -> bitSequence -> bitSequence*)
definition bitSeqArithBinOp  :: "(int \<Rightarrow> int \<Rightarrow> int)\<Rightarrow> bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqArithBinOp binop bs1 bs2 = ( 
  (case  bs1 of
      (BitSeq len1 _ _) =>
  (case  bs2 of
      (BitSeq len2 _ _) =>
  (let len = ((case  (len1, len2) of
                    (Some l1, Some l2) => Some (max l1 l2)
                | _ => None
              )) in
  bitSeqFromInteger len
    (binop (integerFromBitSeq bs1) (integerFromBitSeq bs2)))
  )
  ) )"


(*val bitSeqArithBinTest : forall 'a. (integer -> integer -> 'a) -> bitSequence -> bitSequence -> 'a*)
definition bitSeqArithBinTest  :: "(int \<Rightarrow> int \<Rightarrow> 'a)\<Rightarrow> bitSequence \<Rightarrow> bitSequence \<Rightarrow> 'a "  where 
     " bitSeqArithBinTest binop bs1 bs2 = ( binop (integerFromBitSeq bs1) (integerFromBitSeq bs2))"



(* now instantiate the number interface for bit-sequences *)

(*val bitSeqFromNumeral : numeral -> bitSequence*)

(*val bitSeqLess : bitSequence -> bitSequence -> bool*)
definition bitSeqLess  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bool "  where 
     " bitSeqLess bs1 bs2 = ( bitSeqArithBinTest (op<) bs1 bs2 )"


(*val bitSeqLessEqual : bitSequence -> bitSequence -> bool*)
definition bitSeqLessEqual  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bool "  where 
     " bitSeqLessEqual bs1 bs2 = ( bitSeqArithBinTest (op \<le>) bs1 bs2 )"


(*val bitSeqGreater : bitSequence -> bitSequence -> bool*)
definition bitSeqGreater  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bool "  where 
     " bitSeqGreater bs1 bs2 = ( bitSeqArithBinTest (op>) bs1 bs2 )"


(*val bitSeqGreaterEqual : bitSequence -> bitSequence -> bool*)
definition bitSeqGreaterEqual  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bool "  where 
     " bitSeqGreaterEqual bs1 bs2 = ( bitSeqArithBinTest (op \<ge>) bs1 bs2 )"


(*val bitSeqCompare : bitSequence -> bitSequence -> ordering*)
definition bitSeqCompare  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> ordering "  where 
     " bitSeqCompare bs1 bs2 = ( bitSeqArithBinTest (genericCompare (op<) (op=)) bs1 bs2 )"


definition instance_Basic_classes_Ord_Word_bitSequence_dict  :: "(bitSequence)Ord_class "  where 
     " instance_Basic_classes_Ord_Word_bitSequence_dict = ((|

  compare_method = bitSeqCompare,

  isLess_method = bitSeqLess,

  isLessEqual_method = bitSeqLessEqual,

  isGreater_method = bitSeqGreater,

  isGreaterEqual_method = bitSeqGreaterEqual |) )"


(* arithmetic negation, don't mix up with bitwise negation *)
(*val bitSeqNegate : bitSequence -> bitSequence*) 
definition bitSeqNegate  :: " bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqNegate bs = ( bitSeqArithUnaryOp (\<lambda> i. - i) bs )"


definition instance_Num_NumNegate_Word_bitSequence_dict  :: "(bitSequence)NumNegate_class "  where 
     " instance_Num_NumNegate_Word_bitSequence_dict = ((|

  numNegate_method = bitSeqNegate |) )"



(*val bitSeqAdd : bitSequence -> bitSequence -> bitSequence*)
definition bitSeqAdd  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqAdd bs1 bs2 = ( bitSeqArithBinOp (op+) bs1 bs2 )"


definition instance_Num_NumAdd_Word_bitSequence_dict  :: "(bitSequence)NumAdd_class "  where 
     " instance_Num_NumAdd_Word_bitSequence_dict = ((|

  numAdd_method = bitSeqAdd |) )"


(*val bitSeqMinus : bitSequence -> bitSequence -> bitSequence*)
definition bitSeqMinus  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqMinus bs1 bs2 = ( bitSeqArithBinOp (op-) bs1 bs2 )"


definition instance_Num_NumMinus_Word_bitSequence_dict  :: "(bitSequence)NumMinus_class "  where 
     " instance_Num_NumMinus_Word_bitSequence_dict = ((|

  numMinus_method = bitSeqMinus |) )"


(*val bitSeqSucc : bitSequence -> bitSequence*)
definition bitSeqSucc  :: " bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqSucc bs = ( bitSeqArithUnaryOp (\<lambda> n. n +( 1 :: int)) bs )"


definition instance_Num_NumSucc_Word_bitSequence_dict  :: "(bitSequence)NumSucc_class "  where 
     " instance_Num_NumSucc_Word_bitSequence_dict = ((|

  succ_method = bitSeqSucc |) )"


(*val bitSeqPred : bitSequence -> bitSequence*)
definition bitSeqPred  :: " bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqPred bs = ( bitSeqArithUnaryOp (\<lambda> n. n -( 1 :: int)) bs )"


definition instance_Num_NumPred_Word_bitSequence_dict  :: "(bitSequence)NumPred_class "  where 
     " instance_Num_NumPred_Word_bitSequence_dict = ((|

  pred_method = bitSeqPred |) )"


(*val bitSeqMult : bitSequence -> bitSequence -> bitSequence*)
definition bitSeqMult  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqMult bs1 bs2 = ( bitSeqArithBinOp (op*) bs1 bs2 )"


definition instance_Num_NumMult_Word_bitSequence_dict  :: "(bitSequence)NumMult_class "  where 
     " instance_Num_NumMult_Word_bitSequence_dict = ((|

  numMult_method = bitSeqMult |) )"



(*val bitSeqPow : bitSequence -> nat -> bitSequence*)
definition bitSeqPow  :: " bitSequence \<Rightarrow> nat \<Rightarrow> bitSequence "  where 
     " bitSeqPow bs n = ( bitSeqArithUnaryOp (\<lambda> i .  i ^ n) bs )"


definition instance_Num_NumPow_Word_bitSequence_dict  :: "(bitSequence)NumPow_class "  where 
     " instance_Num_NumPow_Word_bitSequence_dict = ((|

  numPow_method = bitSeqPow |) )"


(*val bitSeqDiv : bitSequence -> bitSequence -> bitSequence*)
definition bitSeqDiv  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqDiv bs1 bs2 = ( bitSeqArithBinOp (op div) bs1 bs2 )"


definition instance_Num_NumIntegerDivision_Word_bitSequence_dict  :: "(bitSequence)NumIntegerDivision_class "  where 
     " instance_Num_NumIntegerDivision_Word_bitSequence_dict = ((|

  div_method = bitSeqDiv |) )"


definition instance_Num_NumDivision_Word_bitSequence_dict  :: "(bitSequence)NumDivision_class "  where 
     " instance_Num_NumDivision_Word_bitSequence_dict = ((|

  numDivision_method = bitSeqDiv |) )"


(*val bitSeqMod : bitSequence -> bitSequence -> bitSequence*)
definition bitSeqMod  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqMod bs1 bs2 = ( bitSeqArithBinOp (op mod) bs1 bs2 )"


definition instance_Num_NumRemainder_Word_bitSequence_dict  :: "(bitSequence)NumRemainder_class "  where 
     " instance_Num_NumRemainder_Word_bitSequence_dict = ((|

  mod_method = bitSeqMod |) )"


(*val bitSeqMin : bitSequence -> bitSequence -> bitSequence*)
definition bitSeqMin  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqMin bs1 bs2 = ( bitSeqArithBinOp min bs1 bs2 )"


(*val bitSeqMax : bitSequence -> bitSequence -> bitSequence*)
definition bitSeqMax  :: " bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence "  where 
     " bitSeqMax bs1 bs2 = ( bitSeqArithBinOp max bs1 bs2 )"


definition instance_Basic_classes_OrdMaxMin_Word_bitSequence_dict  :: "(bitSequence)OrdMaxMin_class "  where 
     " instance_Basic_classes_OrdMaxMin_Word_bitSequence_dict = ((|

  max_method = bitSeqMax,

  min_method = bitSeqMin |) )"





(* ========================================================================== *)
(* Interface for bitoperations                                                *)
(* ========================================================================== *)

record 'a WordNot_class= 

  lnot_method ::" 'a \<Rightarrow> 'a "



record 'a WordAnd_class= 

  land_method  ::" 'a \<Rightarrow> 'a \<Rightarrow> 'a "



record 'a WordOr_class= 

  lor_method ::" 'a \<Rightarrow> 'a \<Rightarrow> 'a "




record 'a WordXor_class= 

  lxor_method ::" 'a \<Rightarrow> 'a \<Rightarrow> 'a "



record 'a WordLsl_class= 

  lsl_method ::" 'a \<Rightarrow> nat \<Rightarrow> 'a "



record 'a WordLsr_class= 

  lsr_method ::" 'a \<Rightarrow> nat \<Rightarrow> 'a "



record 'a WordAsr_class= 

  asr_method ::" 'a \<Rightarrow> nat \<Rightarrow> 'a "



(* ----------------------- *)
(* bitSequence             *)
(* ----------------------- *)

definition instance_Word_WordNot_Word_bitSequence_dict  :: "(bitSequence)WordNot_class "  where 
     " instance_Word_WordNot_Word_bitSequence_dict = ((|

  lnot_method = bitSeqNot |) )"


definition instance_Word_WordAnd_Word_bitSequence_dict  :: "(bitSequence)WordAnd_class "  where 
     " instance_Word_WordAnd_Word_bitSequence_dict = ((|

  land_method = bitSeqAnd |) )"


definition instance_Word_WordOr_Word_bitSequence_dict  :: "(bitSequence)WordOr_class "  where 
     " instance_Word_WordOr_Word_bitSequence_dict = ((|

  lor_method = bitSeqOr |) )"


definition instance_Word_WordXor_Word_bitSequence_dict  :: "(bitSequence)WordXor_class "  where 
     " instance_Word_WordXor_Word_bitSequence_dict = ((|

  lxor_method = bitSeqXor |) )"


definition instance_Word_WordLsl_Word_bitSequence_dict  :: "(bitSequence)WordLsl_class "  where 
     " instance_Word_WordLsl_Word_bitSequence_dict = ((|

  lsl_method = bitSeqShiftLeft |) )"


definition instance_Word_WordLsr_Word_bitSequence_dict  :: "(bitSequence)WordLsr_class "  where 
     " instance_Word_WordLsr_Word_bitSequence_dict = ((|

  lsr_method = bitSeqLogicalShiftRight |) )"


definition instance_Word_WordAsr_Word_bitSequence_dict  :: "(bitSequence)WordAsr_class "  where 
     " instance_Word_WordAsr_Word_bitSequence_dict = ((|

  asr_method = bitSeqArithmeticShiftRight |) )"



(* ----------------------- *)
(* int32                   *)
(* ----------------------- *)

(*val int32Lnot : int32 -> int32*) (* XXX: fix *)

definition instance_Word_WordNot_Num_int32_dict  :: "( 32 word)WordNot_class "  where 
     " instance_Word_WordNot_Num_int32_dict = ((|

  lnot_method = (\<lambda> w. (NOT w))|) )"



(*val int32Lor  : int32 -> int32 -> int32*) (* XXX: fix *)

definition instance_Word_WordOr_Num_int32_dict  :: "( 32 word)WordOr_class "  where 
     " instance_Word_WordOr_Num_int32_dict = ((|

  lor_method = (op OR)|) )"


(*val int32Lxor : int32 -> int32 -> int32*) (* XXX: fix *)

definition instance_Word_WordXor_Num_int32_dict  :: "( 32 word)WordXor_class "  where 
     " instance_Word_WordXor_Num_int32_dict = ((|

  lxor_method = (op XOR)|) )"


(*val int32Land : int32 -> int32 -> int32*) (* XXX: fix *)

definition instance_Word_WordAnd_Num_int32_dict  :: "( 32 word)WordAnd_class "  where 
     " instance_Word_WordAnd_Num_int32_dict = ((|

  land_method = (op AND)|) )"


(*val int32Lsl  : int32 -> nat -> int32*) (* XXX: fix *)

definition instance_Word_WordLsl_Num_int32_dict  :: "( 32 word)WordLsl_class "  where 
     " instance_Word_WordLsl_Num_int32_dict = ((|

  lsl_method = (op<<)|) )"


(*val int32Lsr  : int32 -> nat -> int32*) (* XXX: fix *)

definition instance_Word_WordLsr_Num_int32_dict  :: "( 32 word)WordLsr_class "  where 
     " instance_Word_WordLsr_Num_int32_dict = ((|

  lsr_method = (op>>)|) )"



(*val int32Asr  : int32 -> nat -> int32*) (* XXX: fix *)

definition instance_Word_WordAsr_Num_int32_dict  :: "( 32 word)WordAsr_class "  where 
     " instance_Word_WordAsr_Num_int32_dict = ((|

  asr_method = (op>>>)|) )"



(* ----------------------- *)
(* int64                   *)
(* ----------------------- *)

(*val int64Lnot : int64 -> int64*) (* XXX: fix *)

definition instance_Word_WordNot_Num_int64_dict  :: "( 64 word)WordNot_class "  where 
     " instance_Word_WordNot_Num_int64_dict = ((|

  lnot_method = (\<lambda> w. (NOT w))|) )"


(*val int64Lor  : int64 -> int64 -> int64*) (* XXX: fix *)

definition instance_Word_WordOr_Num_int64_dict  :: "( 64 word)WordOr_class "  where 
     " instance_Word_WordOr_Num_int64_dict = ((|

  lor_method = (op OR)|) )"


(*val int64Lxor : int64 -> int64 -> int64*) (* XXX: fix *)

definition instance_Word_WordXor_Num_int64_dict  :: "( 64 word)WordXor_class "  where 
     " instance_Word_WordXor_Num_int64_dict = ((|

  lxor_method = (op XOR)|) )"


(*val int64Land : int64 -> int64 -> int64*) (* XXX: fix *)

definition instance_Word_WordAnd_Num_int64_dict  :: "( 64 word)WordAnd_class "  where 
     " instance_Word_WordAnd_Num_int64_dict = ((|

  land_method = (op AND)|) )"


(*val int64Lsl  : int64 -> nat -> int64*) (* XXX: fix *)

definition instance_Word_WordLsl_Num_int64_dict  :: "( 64 word)WordLsl_class "  where 
     " instance_Word_WordLsl_Num_int64_dict = ((|

  lsl_method = (op<<)|) )"


(*val int64Lsr  : int64 -> nat -> int64*) (* XXX: fix *)

definition instance_Word_WordLsr_Num_int64_dict  :: "( 64 word)WordLsr_class "  where 
     " instance_Word_WordLsr_Num_int64_dict = ((|

  lsr_method = (op>>)|) )"


(*val int64Asr  : int64 -> nat -> int64*) (* XXX: fix *)

definition instance_Word_WordAsr_Num_int64_dict  :: "( 64 word)WordAsr_class "  where 
     " instance_Word_WordAsr_Num_int64_dict = ((|

  asr_method = (op>>>)|) )"



(* ----------------------- *)
(* Words via bit sequences *)
(* ----------------------- *)

(*val defaultLnot : forall 'a. (bitSequence -> 'a) -> ('a -> bitSequence) -> 'a -> 'a*) 
definition defaultLnot  :: "(bitSequence \<Rightarrow> 'a)\<Rightarrow>('a \<Rightarrow> bitSequence)\<Rightarrow> 'a \<Rightarrow> 'a "  where 
     " defaultLnot fromBitSeq toBitSeq x = ( fromBitSeq (bitSeqNegate (toBitSeq x)))"


(*val defaultLand : forall 'a. (bitSequence -> 'a) -> ('a -> bitSequence) -> 'a -> 'a -> 'a*)
definition defaultLand  :: "(bitSequence \<Rightarrow> 'a)\<Rightarrow>('a \<Rightarrow> bitSequence)\<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a "  where 
     " defaultLand fromBitSeq toBitSeq x1 x2 = ( fromBitSeq (bitSeqAnd (toBitSeq x1) (toBitSeq x2)))"


(*val defaultLor : forall 'a. (bitSequence -> 'a) -> ('a -> bitSequence) -> 'a -> 'a -> 'a*)
definition defaultLor  :: "(bitSequence \<Rightarrow> 'a)\<Rightarrow>('a \<Rightarrow> bitSequence)\<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a "  where 
     " defaultLor fromBitSeq toBitSeq x1 x2 = ( fromBitSeq (bitSeqOr (toBitSeq x1) (toBitSeq x2)))"


(*val defaultLxor : forall 'a. (bitSequence -> 'a) -> ('a -> bitSequence) -> 'a -> 'a -> 'a*)
definition defaultLxor  :: "(bitSequence \<Rightarrow> 'a)\<Rightarrow>('a \<Rightarrow> bitSequence)\<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a "  where 
     " defaultLxor fromBitSeq toBitSeq x1 x2 = ( fromBitSeq (bitSeqXor (toBitSeq x1) (toBitSeq x2)))"


(*val defaultLsl : forall 'a. (bitSequence -> 'a) -> ('a -> bitSequence) -> 'a -> nat -> 'a*)
definition defaultLsl  :: "(bitSequence \<Rightarrow> 'a)\<Rightarrow>('a \<Rightarrow> bitSequence)\<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a "  where 
     " defaultLsl fromBitSeq toBitSeq x n = ( fromBitSeq (bitSeqShiftLeft (toBitSeq x) n))"


(*val defaultLsr : forall 'a. (bitSequence -> 'a) -> ('a -> bitSequence) -> 'a -> nat -> 'a*)
definition defaultLsr  :: "(bitSequence \<Rightarrow> 'a)\<Rightarrow>('a \<Rightarrow> bitSequence)\<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a "  where 
     " defaultLsr fromBitSeq toBitSeq x n = ( fromBitSeq (bitSeqLogicalShiftRight (toBitSeq x) n))"


(*val defaultAsr : forall 'a. (bitSequence -> 'a) -> ('a -> bitSequence) -> 'a -> nat -> 'a*)
definition defaultAsr  :: "(bitSequence \<Rightarrow> 'a)\<Rightarrow>('a \<Rightarrow> bitSequence)\<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a "  where 
     " defaultAsr fromBitSeq toBitSeq x n = ( fromBitSeq (bitSeqArithmeticShiftRight (toBitSeq x) n))"


(* ----------------------- *)
(* integer                 *)
(* ----------------------- *)

(*val integerLnot : integer -> integer*)
definition integerLnot  :: " int \<Rightarrow> int "  where 
     " integerLnot i = ( - (i +( 1 :: int)))"


definition instance_Word_WordNot_Num_integer_dict  :: "(int)WordNot_class "  where 
     " instance_Word_WordNot_Num_integer_dict = ((|

  lnot_method = integerLnot |) )"



(*val integerLor  : integer -> integer -> integer*)
definition integerLor  :: " int \<Rightarrow> int \<Rightarrow> int "  where 
     " integerLor i1 i2 = ( defaultLor integerFromBitSeq (bitSeqFromInteger None) i1 i2 )"


definition instance_Word_WordOr_Num_integer_dict  :: "(int)WordOr_class "  where 
     " instance_Word_WordOr_Num_integer_dict = ((|

  lor_method = integerLor |) )"


(*val integerLxor : integer -> integer -> integer*)
definition integerLxor  :: " int \<Rightarrow> int \<Rightarrow> int "  where 
     " integerLxor i1 i2 = ( defaultLxor integerFromBitSeq (bitSeqFromInteger None) i1 i2 )"


definition instance_Word_WordXor_Num_integer_dict  :: "(int)WordXor_class "  where 
     " instance_Word_WordXor_Num_integer_dict = ((|

  lxor_method = integerLxor |) )"


(*val integerLand : integer -> integer -> integer*)
definition integerLand  :: " int \<Rightarrow> int \<Rightarrow> int "  where 
     " integerLand i1 i2 = ( defaultLand integerFromBitSeq (bitSeqFromInteger None) i1 i2 )"


definition instance_Word_WordAnd_Num_integer_dict  :: "(int)WordAnd_class "  where 
     " instance_Word_WordAnd_Num_integer_dict = ((|

  land_method = integerLand |) )"


(*val integerLsl  : integer -> nat -> integer*)
definition integerLsl  :: " int \<Rightarrow> nat \<Rightarrow> int "  where 
     " integerLsl i n = ( defaultLsl integerFromBitSeq (bitSeqFromInteger None) i n )"


definition instance_Word_WordLsl_Num_integer_dict  :: "(int)WordLsl_class "  where 
     " instance_Word_WordLsl_Num_integer_dict = ((|

  lsl_method = integerLsl |) )"


(*val integerAsr  : integer -> nat -> integer*)
definition integerAsr  :: " int \<Rightarrow> nat \<Rightarrow> int "  where 
     " integerAsr i n = ( defaultAsr integerFromBitSeq (bitSeqFromInteger None) i n )"


definition instance_Word_WordLsr_Num_integer_dict  :: "(int)WordLsr_class "  where 
     " instance_Word_WordLsr_Num_integer_dict = ((|

  lsr_method = integerAsr |) )"


definition instance_Word_WordAsr_Num_integer_dict  :: "(int)WordAsr_class "  where 
     " instance_Word_WordAsr_Num_integer_dict = ((|

  asr_method = integerAsr |) )"



(* ----------------------- *)
(* int                     *)
(* ----------------------- *)

(* sometimes it is convenient to be able to perform bit-operations on ints.
   However, since int is not well-defined (it has different size on different systems),
   it should be used very carefully and only for operations that don't depend on the
   bitwidth of int *)

(*val intFromBitSeq : bitSequence -> int*)
definition intFromBitSeq  :: " bitSequence \<Rightarrow> int "  where 
     " intFromBitSeq bs = (  (integerFromBitSeq (resizeBitSeq (Some(( 31 :: nat))) bs)))"



(*val bitSeqFromInt : int -> bitSequence*) 
definition bitSeqFromInt  :: " int \<Rightarrow> bitSequence "  where 
     " bitSeqFromInt i = ( bitSeqFromInteger (Some(( 31 :: nat))) ( i))"



(*val intLnot : int -> int*)
definition intLnot  :: " int \<Rightarrow> int "  where 
     " intLnot i = ( - (i +( 1 :: int)))"


definition instance_Word_WordNot_Num_int_dict  :: "(int)WordNot_class "  where 
     " instance_Word_WordNot_Num_int_dict = ((|

  lnot_method = intLnot |) )"


(*val intLor  : int -> int -> int*)
definition intLor  :: " int \<Rightarrow> int \<Rightarrow> int "  where 
     " intLor i1 i2 = ( defaultLor intFromBitSeq bitSeqFromInt i1 i2 )"


definition instance_Word_WordOr_Num_int_dict  :: "(int)WordOr_class "  where 
     " instance_Word_WordOr_Num_int_dict = ((|

  lor_method = intLor |) )"


(*val intLxor : int -> int -> int*)
definition intLxor  :: " int \<Rightarrow> int \<Rightarrow> int "  where 
     " intLxor i1 i2 = ( defaultLxor intFromBitSeq bitSeqFromInt i1 i2 )"


definition instance_Word_WordXor_Num_int_dict  :: "(int)WordXor_class "  where 
     " instance_Word_WordXor_Num_int_dict = ((|

  lxor_method = intLxor |) )"


(*val intLand : int -> int -> int*)
definition intLand  :: " int \<Rightarrow> int \<Rightarrow> int "  where 
     " intLand i1 i2 = ( defaultLand intFromBitSeq bitSeqFromInt i1 i2 )"


definition instance_Word_WordAnd_Num_int_dict  :: "(int)WordAnd_class "  where 
     " instance_Word_WordAnd_Num_int_dict = ((|

  land_method = intLand |) )"


(*val intLsl  : int -> nat -> int*)
definition intLsl  :: " int \<Rightarrow> nat \<Rightarrow> int "  where 
     " intLsl i n = ( defaultLsl intFromBitSeq bitSeqFromInt i n )"


definition instance_Word_WordLsl_Num_int_dict  :: "(int)WordLsl_class "  where 
     " instance_Word_WordLsl_Num_int_dict = ((|

  lsl_method = intLsl |) )"


(*val intAsr  : int -> nat -> int*)
definition intAsr  :: " int \<Rightarrow> nat \<Rightarrow> int "  where 
     " intAsr i n = ( defaultAsr intFromBitSeq bitSeqFromInt i n )"


definition instance_Word_WordAsr_Num_int_dict  :: "(int)WordAsr_class "  where 
     " instance_Word_WordAsr_Num_int_dict = ((|

  asr_method = intAsr |) )"




(* ----------------------- *)
(* natural                 *)
(* ----------------------- *)

(* some operations work also on positive numbers *)

(*val naturalFromBitSeq : bitSequence -> natural*)
definition naturalFromBitSeq  :: " bitSequence \<Rightarrow> nat "  where 
     " naturalFromBitSeq bs = ( nat (abs (integerFromBitSeq bs)))"


(*val bitSeqFromNatural : maybe nat -> natural -> bitSequence*)
definition bitSeqFromNatural  :: "(nat)option \<Rightarrow> nat \<Rightarrow> bitSequence "  where 
     " bitSeqFromNatural len n = ( bitSeqFromInteger len (int n))"


(*val naturalLor  : natural -> natural -> natural*)
definition naturalLor  :: " nat \<Rightarrow> nat \<Rightarrow> nat "  where 
     " naturalLor i1 i2 = ( defaultLor naturalFromBitSeq (bitSeqFromNatural None) i1 i2 )"


definition instance_Word_WordOr_Num_natural_dict  :: "(nat)WordOr_class "  where 
     " instance_Word_WordOr_Num_natural_dict = ((|

  lor_method = naturalLor |) )"


(*val naturalLxor : natural -> natural -> natural*)
definition naturalLxor  :: " nat \<Rightarrow> nat \<Rightarrow> nat "  where 
     " naturalLxor i1 i2 = ( defaultLxor naturalFromBitSeq (bitSeqFromNatural None) i1 i2 )"


definition instance_Word_WordXor_Num_natural_dict  :: "(nat)WordXor_class "  where 
     " instance_Word_WordXor_Num_natural_dict = ((|

  lxor_method = naturalLxor |) )"


(*val naturalLand : natural -> natural -> natural*)
definition naturalLand  :: " nat \<Rightarrow> nat \<Rightarrow> nat "  where 
     " naturalLand i1 i2 = ( defaultLand naturalFromBitSeq (bitSeqFromNatural None) i1 i2 )"


definition instance_Word_WordAnd_Num_natural_dict  :: "(nat)WordAnd_class "  where 
     " instance_Word_WordAnd_Num_natural_dict = ((|

  land_method = naturalLand |) )"


(*val naturalLsl  : natural -> nat -> natural*)
definition naturalLsl  :: " nat \<Rightarrow> nat \<Rightarrow> nat "  where 
     " naturalLsl i n = ( defaultLsl naturalFromBitSeq (bitSeqFromNatural None) i n )"


definition instance_Word_WordLsl_Num_natural_dict  :: "(nat)WordLsl_class "  where 
     " instance_Word_WordLsl_Num_natural_dict = ((|

  lsl_method = naturalLsl |) )"


(*val naturalAsr  : natural -> nat -> natural*)
definition naturalAsr  :: " nat \<Rightarrow> nat \<Rightarrow> nat "  where 
     " naturalAsr i n = ( defaultAsr naturalFromBitSeq (bitSeqFromNatural None) i n )"


definition instance_Word_WordLsr_Num_natural_dict  :: "(nat)WordLsr_class "  where 
     " instance_Word_WordLsr_Num_natural_dict = ((|

  lsr_method = naturalAsr |) )"


definition instance_Word_WordAsr_Num_natural_dict  :: "(nat)WordAsr_class "  where 
     " instance_Word_WordAsr_Num_natural_dict = ((|

  asr_method = naturalAsr |) )"



(* ----------------------- *)
(* nat                     *)
(* ----------------------- *)

(* sometimes it is convenient to be able to perform bit-operations on nats.
   However, since nat is not well-defined (it has different size on different systems),
   it should be used very carefully and only for operations that don't depend on the
   bitwidth of nat *)

(*val natFromBitSeq : bitSequence -> nat*)
definition natFromBitSeq  :: " bitSequence \<Rightarrow> nat "  where 
     " natFromBitSeq bs = (  (naturalFromBitSeq (resizeBitSeq (Some(( 31 :: nat))) bs)))"



(*val bitSeqFromNat : nat -> bitSequence*) 
definition bitSeqFromNat  :: " nat \<Rightarrow> bitSequence "  where 
     " bitSeqFromNat i = ( bitSeqFromNatural (Some(( 31 :: nat))) ( i))"



(*val natLor  : nat -> nat -> nat*)
definition natLor  :: " nat \<Rightarrow> nat \<Rightarrow> nat "  where 
     " natLor i1 i2 = ( defaultLor natFromBitSeq bitSeqFromNat i1 i2 )"


definition instance_Word_WordOr_nat_dict  :: "(nat)WordOr_class "  where 
     " instance_Word_WordOr_nat_dict = ((|

  lor_method = natLor |) )"


(*val natLxor : nat -> nat -> nat*)
definition natLxor  :: " nat \<Rightarrow> nat \<Rightarrow> nat "  where 
     " natLxor i1 i2 = ( defaultLxor natFromBitSeq bitSeqFromNat i1 i2 )"


definition instance_Word_WordXor_nat_dict  :: "(nat)WordXor_class "  where 
     " instance_Word_WordXor_nat_dict = ((|

  lxor_method = natLxor |) )"


(*val natLand : nat -> nat -> nat*)
definition natLand  :: " nat \<Rightarrow> nat \<Rightarrow> nat "  where 
     " natLand i1 i2 = ( defaultLand natFromBitSeq bitSeqFromNat i1 i2 )"


definition instance_Word_WordAnd_nat_dict  :: "(nat)WordAnd_class "  where 
     " instance_Word_WordAnd_nat_dict = ((|

  land_method = natLand |) )"


(*val natLsl  : nat -> nat -> nat*)
definition natLsl  :: " nat \<Rightarrow> nat \<Rightarrow> nat "  where 
     " natLsl i n = ( defaultLsl natFromBitSeq bitSeqFromNat i n )"


definition instance_Word_WordLsl_nat_dict  :: "(nat)WordLsl_class "  where 
     " instance_Word_WordLsl_nat_dict = ((|

  lsl_method = natLsl |) )"


(*val natAsr  : nat -> nat -> nat*)
definition natAsr  :: " nat \<Rightarrow> nat \<Rightarrow> nat "  where 
     " natAsr i n = ( defaultAsr natFromBitSeq bitSeqFromNat i n )"


definition instance_Word_WordAsr_nat_dict  :: "(nat)WordAsr_class "  where 
     " instance_Word_WordAsr_nat_dict = ((|

  asr_method = natAsr |) )"


end
