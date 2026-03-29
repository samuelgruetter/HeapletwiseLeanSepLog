import HeapletwiseSepLog.DisjointUnion

abbrev Address := UInt64
abbrev Byte := UInt8
abbrev Mem := Std.ExtHashMap Address Byte

structure Heaplet {Val : Type}
  (relate : Val -> Address -> Mem -> Prop) (val: Val) (addr : Address) : Type
where
  mem : Mem
  connection : relate val addr mem

structure MyRecord where
  x: UInt64
  y: UInt64

section Sketch

variable (myRecord : MyRecord -> Address -> Mem -> Prop)

variable (uint : Nat -> Nat -> Address -> Mem -> Prop)

variable (array : forall {E : Type}, (E -> Address -> Mem -> Prop) -> Nat ->
  List Nat -> Address -> Mem -> Prop)
 /- TODO where to put elem size/offset between elements? Infer using typeclass? -/

variable (Instr : Type)

variable (wp : List Instr -> Mem -> (Mem -> Prop) -> Prop)

variable (incFieldX : List Instr)

theorem incFieldX_correct (a_r : Address) (a_vs : Address)
  (r : MyRecord) (vs : List Nat)
  (h_r : Heaplet myRecord r a_r)
  (h_vs : Heaplet (array (uint 8) 16) vs a_vs)
  (boundX : r.x.toNat < UInt64.size - 1)
  (m : Mem)
  (D : m.splits [h_r.mem, h_vs.mem])
  (post : Mem -> Prop):
  (forall h_r' : Heaplet myRecord { r with x := r.x + 1 } a_r,
    m.splits [h_r'.mem, h_vs.mem] ->
    post m) ->
  wp incFieldX m post
  := by sorry

end Sketch
