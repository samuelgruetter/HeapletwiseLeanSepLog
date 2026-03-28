import HeapletwiseLeanSepLog.DisjointUnion

private def mm (pairs: List (UInt32 × UInt8)) : MMap UInt32 UInt8 :=
  MMap.some (Std.ExtHashMap.ofList pairs)

/- Note: we cannot use kernel reduction/rfl because Std.ExtHashMap is defined as a quotient -/

example: (mm [(1, 10), (2, 20), (3, 30)]).subtract (mm [(2, 20)]) = mm [(1, 10), (3, 30)] :=
  by native_decide

example: (mm [(1, 10), (2, 20)]).subtract (mm [(1, 10), (2, 20)]) = ∅ :=
  by native_decide

example: (mm [(1, 10), (2, 20)]).subtract (mm [(1, 10), (2, 222)]) = .none :=
  by native_decide
