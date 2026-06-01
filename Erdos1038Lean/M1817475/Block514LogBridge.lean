import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block514

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block514

open Set

def block514W1 : Rat := ((42524964695646233 : Rat) / 100000000000000000)
def block514W2 : Rat := (0 : Rat)
def block514W3 : Rat := ((22277051753150373 : Rat) / 50000000000000000)
def block514W4 : Rat := ((4598872963920241 : Rat) / 10000000000000000000)
def block514S1 : Rat := ((18174751 : Rat) / 10000000)
def block514S2 : Rat := ((511587 : Rat) / 200000)
def block514S3 : Rat := ((1040682529285714287 : Rat) / 400000000000000000)
def block514S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block514V (y : ℝ) : ℝ :=
  ratPotential block514W1 block514W2 block514W3 block514W4 block514S1 block514S2 block514S3 block514S4 y

def block514LeftParamsCertificate : Bool :=
  allBoxesSameParams block514LeftBoxes block514W1 block514W2 block514W3 block514W4 block514S1 block514S2 block514S3 block514S4

theorem block514LeftParamsCertificate_eq_true :
    block514LeftParamsCertificate = true := by
  native_decide

theorem block514_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block514LeftL : ℝ) (block514LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block514S1 : ℝ))
    (hy2ne : y ≠ (block514S2 : ℝ))
    (hy3ne : y ≠ (block514S3 : ℝ))
    (hy4ne : y ≠ (block514S4 : ℝ)) :
    0 < block514V y := by
  have hcert := block514LeftCertificate_eq_true
  unfold block514LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block514LeftBoxes) (lo := block514LeftL) (hi := block514LeftR)
    (w1 := block514W1) (w2 := block514W2) (w3 := block514W3) (w4 := block514W4)
    (s1 := block514S1) (s2 := block514S2) (s3 := block514S3) (s4 := block514S4)
    hboxes hcover block514LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block514RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block514RightChunk000 block514W1 block514W2 block514W3 block514W4 block514S1 block514S2 block514S3 block514S4

theorem block514RightChunk000ParamsCertificate_eq_true :
    block514RightChunk000ParamsCertificate = true := by
  native_decide

theorem block514_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block514RightChunk000L : ℝ) (block514RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block514S1 : ℝ))
    (hy2ne : y ≠ (block514S2 : ℝ))
    (hy3ne : y ≠ (block514S3 : ℝ))
    (hy4ne : y ≠ (block514S4 : ℝ)) :
    0 < block514V y := by
  have hcert := block514RightChunk000Certificate_eq_true
  unfold block514RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block514RightChunk000) (lo := block514RightChunk000L) (hi := block514RightChunk000R)
    (w1 := block514W1) (w2 := block514W2) (w3 := block514W3) (w4 := block514W4)
    (s1 := block514S1) (s2 := block514S2) (s3 := block514S3) (s4 := block514S4)
    hboxes hcover block514RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block514_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block514RightL : ℝ) (block514RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block514S1 : ℝ))
    (hy2ne : y ≠ (block514S2 : ℝ))
    (hy3ne : y ≠ (block514S3 : ℝ))
    (hy4ne : y ≠ (block514S4 : ℝ)) :
    0 < block514V y := by
  have hL : (block514RightChunk000L : ℝ) = (block514RightL : ℝ) := by
    norm_num [block514RightChunk000L, block514RightL]
  have hR : (block514RightChunk000R : ℝ) = (block514RightR : ℝ) := by
    norm_num [block514RightChunk000R, block514RightR]
  have hyc : y ∈ Icc (block514RightChunk000L : ℝ) (block514RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block514_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block514_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block514LeftL : ℝ) (block514LeftR : ℝ) →
    y ≠ 0 → y ≠ (block514S1 : ℝ) → y ≠ (block514S2 : ℝ) →
    y ≠ (block514S3 : ℝ) → y ≠ (block514S4 : ℝ) → 0 < block514V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block514RightL : ℝ) (block514RightR : ℝ) →
    y ≠ 0 → y ≠ (block514S1 : ℝ) → y ≠ (block514S2 : ℝ) →
    y ≠ (block514S3 : ℝ) → y ≠ (block514S4 : ℝ) → 0 < block514V y)

theorem block514_reallog_certificate_proof :
    block514_reallog_certificate := by
  exact ⟨block514_left_V_pos, block514_right_V_pos⟩

end Block514
end M1817475
end Erdos1038Lean
