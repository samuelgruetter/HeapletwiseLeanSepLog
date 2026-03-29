import HeapletwiseLeanSepLog.DisjointUnion

abbrev Address := UInt64
abbrev Byte := UInt8
abbrev Mem := Std.ExtHashMap Address Byte

inductive OnHeapAt
  {T : Type} (encode : T -> Address -> Option Mem) (addr : Address) : Type
where
  | mk (val : T) (mem : Mem) (connection : encode val addr = some mem)

infix:80 " @ " => OnHeapAt /- TODO will this class with @make_implicit_args_explicit ? -/
