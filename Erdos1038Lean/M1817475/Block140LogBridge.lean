import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block140

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block140

open Set

def block140W1 : Rat := ((6293273010862953 : Rat) / 2500000000000000)
def block140W2 : Rat := (0 : Rat)
def block140W3 : Rat := ((1220612945820441 : Rat) / 10000000000000000)
def block140W4 : Rat := ((11724509260545421 : Rat) / 100000000000000000)
def block140S1 : Rat := ((18174751 : Rat) / 10000000)
def block140S2 : Rat := ((511587 : Rat) / 200000)
def block140S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block140S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block140V (y : ℝ) : ℝ :=
  ratPotential block140W1 block140W2 block140W3 block140W4 block140S1 block140S2 block140S3 block140S4 y

def block140LeftParamsCertificate : Bool :=
  allBoxesSameParams block140LeftBoxes block140W1 block140W2 block140W3 block140W4 block140S1 block140S2 block140S3 block140S4

theorem block140LeftParamsCertificate_eq_true :
    block140LeftParamsCertificate = true := by
  native_decide

theorem block140_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block140LeftL : ℝ) (block140LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block140S1 : ℝ))
    (hy2ne : y ≠ (block140S2 : ℝ))
    (hy3ne : y ≠ (block140S3 : ℝ))
    (hy4ne : y ≠ (block140S4 : ℝ)) :
    0 < block140V y := by
  have hcert := block140LeftCertificate_eq_true
  unfold block140LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block140LeftBoxes) (lo := block140LeftL) (hi := block140LeftR)
    (w1 := block140W1) (w2 := block140W2) (w3 := block140W3) (w4 := block140W4)
    (s1 := block140S1) (s2 := block140S2) (s3 := block140S3) (s4 := block140S4)
    hboxes hcover block140LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block140RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block140RightChunk000 block140W1 block140W2 block140W3 block140W4 block140S1 block140S2 block140S3 block140S4

theorem block140RightChunk000ParamsCertificate_eq_true :
    block140RightChunk000ParamsCertificate = true := by
  native_decide

theorem block140_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block140RightChunk000L : ℝ) (block140RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block140S1 : ℝ))
    (hy2ne : y ≠ (block140S2 : ℝ))
    (hy3ne : y ≠ (block140S3 : ℝ))
    (hy4ne : y ≠ (block140S4 : ℝ)) :
    0 < block140V y := by
  have hcert := block140RightChunk000Certificate_eq_true
  unfold block140RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block140RightChunk000) (lo := block140RightChunk000L) (hi := block140RightChunk000R)
    (w1 := block140W1) (w2 := block140W2) (w3 := block140W3) (w4 := block140W4)
    (s1 := block140S1) (s2 := block140S2) (s3 := block140S3) (s4 := block140S4)
    hboxes hcover block140RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block140_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block140RightL : ℝ) (block140RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block140S1 : ℝ))
    (hy2ne : y ≠ (block140S2 : ℝ))
    (hy3ne : y ≠ (block140S3 : ℝ))
    (hy4ne : y ≠ (block140S4 : ℝ)) :
    0 < block140V y := by
  have hL : (block140RightChunk000L : ℝ) = (block140RightL : ℝ) := by
    norm_num [block140RightChunk000L, block140RightL]
  have hR : (block140RightChunk000R : ℝ) = (block140RightR : ℝ) := by
    norm_num [block140RightChunk000R, block140RightR]
  have hyc : y ∈ Icc (block140RightChunk000L : ℝ) (block140RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block140_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block140_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block140LeftL : ℝ) (block140LeftR : ℝ) →
    y ≠ 0 → y ≠ (block140S1 : ℝ) → y ≠ (block140S2 : ℝ) →
    y ≠ (block140S3 : ℝ) → y ≠ (block140S4 : ℝ) → 0 < block140V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block140RightL : ℝ) (block140RightR : ℝ) →
    y ≠ 0 → y ≠ (block140S1 : ℝ) → y ≠ (block140S2 : ℝ) →
    y ≠ (block140S3 : ℝ) → y ≠ (block140S4 : ℝ) → 0 < block140V y)

theorem block140_reallog_certificate_proof :
    block140_reallog_certificate := by
  exact ⟨block140_left_V_pos, block140_right_V_pos⟩

end Block140
end M1817475
end Erdos1038Lean
