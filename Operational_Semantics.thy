theory Operational_Semantics
  imports Syntax State
begin

datatype ctx_arith = Hole | Add1 ctx_arith arith | Add2 int ctx_arith | Mult1 ctx_arith arith | Mult2 int ctx_arith | Sub1 ctx_arith arith | Sub2 int ctx_arith
datatype inst_arith = IVar var | IAdd int int | IMult int int | ISub int int
datatype inst_arith_res = AInst ctx_arith inst_arith | Num int

fun to_inst_arith :: "arith \<Rightarrow> inst_arith_res"
  where "to_inst_arith (AInt n) = Num n"
      | "to_inst_arith (AVar v) = AInst Hole (IVar v)"
      | "to_inst_arith (AAdd a1 a2) = (case (to_inst_arith a1, to_inst_arith a2)
        of (Num n1, Num n2) \<Rightarrow> AInst Hole (IAdd n1 n2)
         | (Num n, AInst c i) \<Rightarrow> AInst (Add2 n c) i
         | (AInst c i, _) \<Rightarrow> AInst (Add1 c a2) i)"
      | "to_inst_arith (AMult a1 a2) = (case (to_inst_arith a1, to_inst_arith a2)
        of (Num n1, Num n2) \<Rightarrow> AInst Hole (IMult n1 n2)
         | (Num n, AInst c i) \<Rightarrow> AInst (Mult2 n c) i
         | (AInst c i, _) \<Rightarrow> AInst (Mult1 c a2) i)"
      | "to_inst_arith (ASub a1 a2) = (case (to_inst_arith a1, to_inst_arith a2)
        of (Num n1, Num n2) \<Rightarrow> AInst Hole (ISub n1 n2)
         | (Num n, AInst c i) \<Rightarrow> AInst (Sub2 n c) i
         | (AInst c i, _) \<Rightarrow> AInst (Sub1 c a2) i)"

fun plug_arith :: "ctx_arith \<Rightarrow> arith \<Rightarrow> arith"
  where "plug_arith Hole a = a"
      | "plug_arith (Add1 c a) a' = AAdd (plug_arith c a') a"
      | "plug_arith (Add2 n c) a' = AAdd (AInt n) (plug_arith c a')"
      | "plug_arith (Mult1 c a) a' = AMult (plug_arith c a') a"
      | "plug_arith (Mult2 n c) a' = AMult (AInt n) (plug_arith c a')"
      | "plug_arith (Sub1 c a) a' = ASub (plug_arith c a') a"
      | "plug_arith (Sub2 n c) a' = ASub (AInt n) (plug_arith c a')"

lemma
  assumes X_def: "X = AVar 1"
      and Y_def: "Y = AVar 2"
    shows "to_inst_arith (AAdd (AMult X (AInt 3)) Y) = AInst (Add1 (Mult1 Hole (AInt 3)) Y) (IVar 1)"
unfolding X_def Y_def by simp

lemma
  assumes Y_def: "Y = AVar 2"
    shows "to_inst_arith (AAdd (AMult (AInt 2) (AInt 3)) Y) = AInst (Add1 Hole Y) (IMult 2 3)"
unfolding Y_def by simp

fun reduce_arith :: "arith \<Rightarrow> state \<Rightarrow> (arith \<times> state) option"
  where "reduce_arith a s = (case to_inst_arith a
    of AInst c (IVar v) \<Rightarrow> (case lookup s v of Some n \<Rightarrow> Some (plug_arith c (AInt n), s) | None \<Rightarrow> None)
     | AInst c (IAdd n1 n2) \<Rightarrow> Some (plug_arith c (AInt (n1 + n2)), s)
     | AInst c (IMult n1 n2) \<Rightarrow> Some (plug_arith c (AInt (n1 * n2)), s)
     | AInst c (ISub n1 n2) \<Rightarrow> Some (plug_arith c (AInt (n1 - n2)), s))"

lemma
  fixes s :: state
  assumes X_def: "X = 0"
      and Y_def: "Y = 1"
      and s_X_eq: "lookup s X = Some 2"
      and s_Y_eq: "lookup s Y = Some 1"
  shows "reduce_arith (AAdd (AMult (AVar X) (AInt 3)) (AVar Y)) s = Some (AAdd (AMult (AInt 2) (AInt 3)) (AVar Y), s)" by (simp add: s_X_eq)

lemma
  fixes s :: state
  assumes X_def: "X = 0"
      and Y_def: "Y = 1"
      and s_X_eq: "lookup s X = Some 2"
      and s_Y_eq: "lookup s Y = Some 1"
  shows "reduce_arith (AAdd (AMult (AInt 2) (AInt 3)) (AVar Y)) s = Some ((AAdd (AInt 6) (AVar Y)), s)" by simp

lemma
  fixes s :: state
  assumes X_def: "X = 0"
      and Y_def: "Y = 1"
      and s_X_eq: "lookup s X = Some 2"
      and s_Y_eq: "lookup s Y = Some 1"
  shows "reduce_arith (AAdd (AInt 6) (AVar Y)) s = Some ((AAdd (AInt 6) (AInt 1)), s)" by (simp add: s_Y_eq)

lemma
  fixes s :: state
  assumes X_def: "X = 0"
      and Y_def: "Y = 1"
      and s_X_eq: "lookup s X = Some 2"
      and s_Y_eq: "lookup s Y = Some 1"
  shows "reduce_arith (AAdd (AInt 6) (AInt 1)) s = Some ((AInt 7), s)" by simp

datatype ctx_bexp = Hole | Not ctx_bexp | And1 ctx_bexp bexp | And2 bool ctx_bexp
datatype inst_bexp = ILessEq arith arith | INot bool | IAnd bool bool
datatype inst_bexp_res = BInst ctx_bexp inst_bexp | Bool bool

fun to_inst_bexp :: "bexp \<Rightarrow> inst_bexp_res"
  where "to_inst_bexp (BBool b) = Bool b"
      | "to_inst_bexp (BLessEq a1 a2) = BInst Hole (ILessEq a1 a2)"
      | "to_inst_bexp (BNot b) = (case to_inst_bexp b
         of Bool b \<Rightarrow> BInst Hole (INot b)
          | BInst c i \<Rightarrow> BInst (Not c) i)"
      | "to_inst_bexp (BAnd b1 b2) = (case (to_inst_bexp b1, to_inst_bexp b2)
        of (Bool b1, Bool b2) \<Rightarrow> BInst Hole (IAnd b1 b2)
         | (Bool b1, BInst b2 i) \<Rightarrow> BInst (And2 b1 b2) i
         | (BInst b i, _) \<Rightarrow> BInst (And1 b b2) i)"

fun plug_bexp :: "ctx_bexp \<Rightarrow> bexp \<Rightarrow> bexp"
  where "plug_bexp Hole b = b"
      | "plug_bexp (Not c) b' = BNot (plug_bexp c b')"
      | "plug_bexp (And1 c b) b' = BAnd (plug_bexp c b') b"
      | "plug_bexp (And2 b c) b' = BAnd (BBool b) (plug_bexp c b')"

fun reduce_bexp :: "bexp \<Rightarrow> state \<Rightarrow> (bexp \<times> state) option"
  where "reduce_bexp b s = (case to_inst_bexp b
    of Bool _ \<Rightarrow> None
     | BInst c (ILessEq (AInt n1) (AInt n2)) \<Rightarrow> Some (plug_bexp c (BBool (n1 \<le> n2)), s)
     | BInst c (ILessEq (AInt n1) a2) \<Rightarrow> (case reduce_arith a2 s
       of Some (a2', s') \<Rightarrow> Some (plug_bexp c (BLessEq (AInt n1) a2'), s')
        | None \<Rightarrow> None)
     | BInst c (ILessEq a1 a2) \<Rightarrow> (case reduce_arith a1 s
       of Some (a1', s') \<Rightarrow> Some (plug_bexp c (BLessEq a1' a2), s'))
     | BInst c (INot b) \<Rightarrow> Some (plug_bexp c (BBool (\<not> b)), s)
     | BInst c (IAnd b1 b2) \<Rightarrow> Some (plug_bexp c (BBool (b1 \<and> b2)), s))"

lemma
  assumes X_def: "X = 0"
      and Y_def: "Y = 1"
      and s_X_eq: "lookup s X = Some 2"
      and s_Y_eq: "lookup s Y = Some 1"
    shows "reduce_bexp (BAnd (BLessEq (AVar X) (AInt 2)) (BLessEq (AInt 2) (AVar Y))) s = Some (BAnd (BLessEq (AInt 2) (AInt 2)) (BLessEq (AInt 2) (AVar Y)), s)" by (simp add: s_X_eq)

lemma
  assumes X_def: "X = 0"
      and Y_def: "Y = 1"
      and s_X_eq: "lookup s X = Some 2"
      and s_Y_eq: "lookup s Y = Some 1"
    shows "reduce_bexp (BAnd (BLessEq (AInt 2) (AInt 2)) (BLessEq (AInt 2) (AVar Y))) s = Some (BAnd (BBool True) (BLessEq (AInt 2) (AVar Y)), s)" by simp

lemma
  assumes X_def: "X = 0"
      and Y_def: "Y = 1"
      and s_X_eq: "lookup s X = Some 2"
      and s_Y_eq: "lookup s Y = Some 1"
    shows "reduce_bexp (BAnd (BBool True) (BLessEq (AInt 2) (AVar Y))) s = Some (BAnd (BBool True) (BLessEq (AInt 2) (AInt 1)), s)" by (simp add: s_Y_eq)

lemma
  assumes X_def: "X = 0"
      and Y_def: "Y = 1"
      and s_X_eq: "lookup s X = Some 2"
      and s_Y_eq: "lookup s Y = Some 1"
    shows "reduce_bexp (BAnd (BBool True) (BLessEq (AInt 2) (AInt 1))) s = Some (BAnd (BBool True) (BBool False), s)" by simp

lemma
  assumes X_def: "X = 0"
      and Y_def: "Y = 1"
      and s_X_eq: "lookup s X = Some 2"
      and s_Y_eq: "lookup s Y = Some 1"
    shows "reduce_bexp (BAnd (BBool True) (BBool False)) s = Some (BBool False, s)" by simp

datatype ctx_prog = Hole | Seq ctx_prog prog
datatype inst_prog = ISkip prog | IAssg var arith | IIf bexp prog prog | IWhile bexp prog
datatype inst_prog_res = PInst ctx_prog inst_prog | IRSkip

fun to_inst_prog :: "prog \<Rightarrow> inst_prog_res"
  where "to_inst_prog PSkip = IRSkip"
      | "to_inst_prog (PAssg v a) = PInst Hole (IAssg v a)"
      | "to_inst_prog (PSeq p1 p2) = (case to_inst_prog p1
        of PInst c i \<Rightarrow> PInst (Seq c p2) i
         | IRSkip \<Rightarrow> PInst Hole (ISkip p2))"
      | "to_inst_prog (PIf b p1 p2) = PInst Hole (IIf b p1 p2)"
      | "to_inst_prog (PWhile b p) = PInst Hole (IWhile b p)"      

fun plug_prog :: "ctx_prog \<Rightarrow> prog \<Rightarrow> prog"
  where "plug_prog Hole p = p"
      | "plug_prog (Seq c p) p' = PSeq (plug_prog c p') p"

fun reduce_prog :: "prog \<Rightarrow> state \<Rightarrow> (prog \<times> state) option"
  where "reduce_prog p s = (case to_inst_prog p
    of IRSkip \<Rightarrow> None
     | PInst c (ISkip p) \<Rightarrow> Some (plug_prog c p, s)
     | PInst c (IAssg v (AInt n)) \<Rightarrow> Some (plug_prog c PSkip, state_upd s v (Some n))
     | PInst c (IAssg v a) \<Rightarrow> (case reduce_arith a s
        of None \<Rightarrow> None
         | Some (a', s') \<Rightarrow> Some (plug_prog c (PAssg v a'), s'))
     | PInst c (IIf (BBool True) p1 _) \<Rightarrow> Some (plug_prog c p1, s)
     | PInst c (IIf (BBool False) _ p2) \<Rightarrow> Some (plug_prog c p2, s)
     | PInst c (IIf b p1 p2) \<Rightarrow> (case reduce_bexp b s
        of None \<Rightarrow> None
         | Some (b', s') \<Rightarrow> Some (plug_prog c (PIf b' p1 p2), s'))
     | PInst c (IWhile b p) \<Rightarrow> Some (plug_prog c (PIf b (PSeq p (PWhile b p)) PSkip), s))"

lemma
  assumes X_def: "X = 0"
      and S_def: "S = 1"
      and c_def: "c = PWhile
        (BLessEq (AInt 1) (AVar X))
        (PSeq
          (PAssg S (AAdd (AVar S) (AVar X)))
          (PAssg X (ASub (AVar X) (AInt 1)))
        )"
      and s_X_eq: "lookup s X = Some 2"
      and s_S_eq: "lookup s S = Some 0"
    shows "reduce_prog c s = Some (
      PIf
        (BLessEq (AInt 1) (AVar X))
        (PSeq
          (PSeq
            (PAssg S (AAdd (AVar S) (AVar X)))
            (PAssg X (ASub (AVar X) (AInt 1)))
          )
          c
        )
        PSkip,
      s
    )" unfolding c_def by simp

end