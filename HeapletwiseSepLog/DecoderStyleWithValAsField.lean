import HeapletwiseSepLog.DisjointUnion

abbrev Address := UInt64
abbrev Byte := UInt8
abbrev Mem := Std.ExtHashMap Address Byte

structure OnHeapAt
  {T : Type} (decode : Mem -> Address -> Option T) (addr : Address) : Type
where
  val : T
  mem : Mem
  connection : decode mem addr = some val

infix:80 " @ " => OnHeapAt /- TODO will this class with @make_implicit_args_explicit ? -/

structure MyRecord where
  x: UInt64
  y: UInt64

def myRecord (m : Mem) (a : Address) : Option MyRecord := by sorry

def uint (bitwidth : Nat) (m : Mem) (addr : Address) : Option Nat := by sorry

def array {E : Type} (elem : Mem -> Address -> Option E) (len : Nat) (m : Mem) (a : Address)
    : Option (List E) :=
  by sorry /- TODO where to put elem size/offset between elements? Infer using typeclass? -/

def Instr : Type := by sorry

def wp (prog : List Instr) (initial : Mem) (post : Mem -> Prop) : Prop := by sorry

def incFieldX : List Instr := by sorry

theorem incFieldX_correct (a_r : Address) (a_vs : Address)
  (r : myRecord @ a_r)
  (vs : (array (uint 8) 16) @ a_vs)
  (boundX : r.val.x.toNat < UInt64.size - 1)
  (m : Mem)
  (D : m.splits [r.mem, vs.mem])
  (post : Mem -> Prop):
  (forall r' : myRecord @ a_r,
    r'.val.x == r.val.x + 1 ->
    r'.val.y == r.val.y ->
    m.splits [r'.mem, vs.mem] ->
    post m) ->
  wp incFieldX m post
  := by sorry
