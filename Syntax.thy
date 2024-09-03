theory Syntax
  imports Main
begin

type_synonym var = nat
datatype arith = AInt int | AVar var | AAdd arith arith | AMult arith arith | ASub arith arith
datatype bexp = BBool bool | BLessEq arith arith | BNot bexp | BAnd bexp bexp
datatype prog = PSkip | PAssg var arith | PSeq prog prog | PIf bexp prog prog | PWhile bexp prog

end