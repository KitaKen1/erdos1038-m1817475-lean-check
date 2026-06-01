import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block439

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block439

open Set

def block439W1 : Rat := ((1573932852992669 : Rat) / 2500000000000000)
def block439W2 : Rat := (0 : Rat)
def block439W3 : Rat := ((31866341071949317 : Rat) / 100000000000000000)
def block439W4 : Rat := ((3727416052247009 : Rat) / 50000000000000000)
def block439S1 : Rat := ((18174751 : Rat) / 10000000)
def block439S2 : Rat := ((511587 : Rat) / 200000)
def block439S3 : Rat := ((5262059967857142861 : Rat) / 2000000000000000000)
def block439S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block439V (y : ℝ) : ℝ :=
  ratPotential block439W1 block439W2 block439W3 block439W4 block439S1 block439S2 block439S3 block439S4 y

def block439LeftParamsCertificate : Bool :=
  allBoxesSameParams block439LeftBoxes block439W1 block439W2 block439W3 block439W4 block439S1 block439S2 block439S3 block439S4

theorem block439LeftParamsCertificate_eq_true :
    block439LeftParamsCertificate = true := by
  native_decide

theorem block439_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block439LeftL : ℝ) (block439LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block439S1 : ℝ))
    (hy2ne : y ≠ (block439S2 : ℝ))
    (hy3ne : y ≠ (block439S3 : ℝ))
    (hy4ne : y ≠ (block439S4 : ℝ)) :
    0 < block439V y := by
  have hcert := block439LeftCertificate_eq_true
  unfold block439LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block439LeftBoxes) (lo := block439LeftL) (hi := block439LeftR)
    (w1 := block439W1) (w2 := block439W2) (w3 := block439W3) (w4 := block439W4)
    (s1 := block439S1) (s2 := block439S2) (s3 := block439S3) (s4 := block439S4)
    hboxes hcover block439LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block439RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block439RightChunk000 block439W1 block439W2 block439W3 block439W4 block439S1 block439S2 block439S3 block439S4

theorem block439RightChunk000ParamsCertificate_eq_true :
    block439RightChunk000ParamsCertificate = true := by
  native_decide

theorem block439_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block439RightChunk000L : ℝ) (block439RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block439S1 : ℝ))
    (hy2ne : y ≠ (block439S2 : ℝ))
    (hy3ne : y ≠ (block439S3 : ℝ))
    (hy4ne : y ≠ (block439S4 : ℝ)) :
    0 < block439V y := by
  have hcert := block439RightChunk000Certificate_eq_true
  unfold block439RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block439RightChunk000) (lo := block439RightChunk000L) (hi := block439RightChunk000R)
    (w1 := block439W1) (w2 := block439W2) (w3 := block439W3) (w4 := block439W4)
    (s1 := block439S1) (s2 := block439S2) (s3 := block439S3) (s4 := block439S4)
    hboxes hcover block439RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block439_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block439RightL : ℝ) (block439RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block439S1 : ℝ))
    (hy2ne : y ≠ (block439S2 : ℝ))
    (hy3ne : y ≠ (block439S3 : ℝ))
    (hy4ne : y ≠ (block439S4 : ℝ)) :
    0 < block439V y := by
  have hL : (block439RightChunk000L : ℝ) = (block439RightL : ℝ) := by
    norm_num [block439RightChunk000L, block439RightL]
  have hR : (block439RightChunk000R : ℝ) = (block439RightR : ℝ) := by
    norm_num [block439RightChunk000R, block439RightR]
  have hyc : y ∈ Icc (block439RightChunk000L : ℝ) (block439RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block439_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block439_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block439LeftL : ℝ) (block439LeftR : ℝ) →
    y ≠ 0 → y ≠ (block439S1 : ℝ) → y ≠ (block439S2 : ℝ) →
    y ≠ (block439S3 : ℝ) → y ≠ (block439S4 : ℝ) → 0 < block439V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block439RightL : ℝ) (block439RightR : ℝ) →
    y ≠ 0 → y ≠ (block439S1 : ℝ) → y ≠ (block439S2 : ℝ) →
    y ≠ (block439S3 : ℝ) → y ≠ (block439S4 : ℝ) → 0 < block439V y)

theorem block439_reallog_certificate_proof :
    block439_reallog_certificate := by
  exact ⟨block439_left_V_pos, block439_right_V_pos⟩

end Block439
end M1817475
end Erdos1038Lean
