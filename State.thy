theory State
  imports PFun Syntax
begin

type_synonym state = "(var, int) pfun"

definition lookup :: "state \<Rightarrow> var \<Rightarrow> int option"
  where "lookup s v = (Rep_pfun s v)"

definition state_upd :: "state \<Rightarrow> var \<Rightarrow> int option \<Rightarrow> state"
  where "state_upd s v n = Abs_pfun ((Rep_pfun s)(v:=n))"

lemma lookup_state_upd[simp]: "lookup (state_upd s v n) v = n"
unfolding lookup_def state_upd_def by (simp add: Abs_pfun_inverse)

end