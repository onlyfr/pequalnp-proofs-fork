import PEqualNP.Outside.PrivateForestLift

namespace Onlyfr.ThreeEdgeProjection

def ends (v : Fin 6 → α) (i : Fin 3) : α × α :=
  (v ⟨2*i.val,by omega⟩, v ⟨2*i.val+1,by omega⟩)

def colors (star : Bool) : Fin 3 → Fin 4 × Fin 4 :=
  if star then ![(3,0),(3,1),(3,2)] else ![(0,1),(1,2),(2,0)]

end Onlyfr.ThreeEdgeProjection
