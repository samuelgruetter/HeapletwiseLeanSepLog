import HeapletwiseLeanSepLog.DisjointUnion

abbrev Address := UInt64
abbrev Byte := UInt8
abbrev Mem := Std.ExtHashMap Address Byte

inductive OnHeapAt
  {T : Type} (relate : T -> Address -> Mem -> Prop) (addr : Address) : Type
where
  | mk (val : T) (mem : Mem) (connection : relate val addr mem)

infix:80 " @ " => OnHeapAt /- TODO will this class with @make_implicit_args_explicit ? -/
