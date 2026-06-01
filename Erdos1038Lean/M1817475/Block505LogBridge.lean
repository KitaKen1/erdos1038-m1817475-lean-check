import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block505

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block505

open Set

def block505W1 : Rat := ((4486510889478307 : Rat) / 10000000000000000)
def block505W2 : Rat := (0 : Rat)
def block505W3 : Rat := ((42545532717290413 : Rat) / 100000000000000000)
def block505W4 : Rat := ((2658557356613973 : Rat) / 200000000000000000)
def block505S1 : Rat := ((18174751 : Rat) / 10000000)
def block505S2 : Rat := ((511587 : Rat) / 200000)
def block505S3 : Rat := ((130261258125000000153 : Rat) / 50000000000000000000)
def block505S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block505V (y : ℝ) : ℝ :=
  ratPotential block505W1 block505W2 block505W3 block505W4 block505S1 block505S2 block505S3 block505S4 y

def block505LeftParamsCertificate : Bool :=
  allBoxesSameParams block505LeftBoxes block505W1 block505W2 block505W3 block505W4 block505S1 block505S2 block505S3 block505S4

theorem block505LeftParamsCertificate_eq_true :
    block505LeftParamsCertificate = true := by
  native_decide

theorem block505_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block505LeftL : ℝ) (block505LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block505S1 : ℝ))
    (hy2ne : y ≠ (block505S2 : ℝ))
    (hy3ne : y ≠ (block505S3 : ℝ))
    (hy4ne : y ≠ (block505S4 : ℝ)) :
    0 < block505V y := by
  have hcert := block505LeftCertificate_eq_true
  unfold block505LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block505LeftBoxes) (lo := block505LeftL) (hi := block505LeftR)
    (w1 := block505W1) (w2 := block505W2) (w3 := block505W3) (w4 := block505W4)
    (s1 := block505S1) (s2 := block505S2) (s3 := block505S3) (s4 := block505S4)
    hboxes hcover block505LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block505RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block505RightChunk000 block505W1 block505W2 block505W3 block505W4 block505S1 block505S2 block505S3 block505S4

theorem block505RightChunk000ParamsCertificate_eq_true :
    block505RightChunk000ParamsCertificate = true := by
  native_decide

theorem block505_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block505RightChunk000L : ℝ) (block505RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block505S1 : ℝ))
    (hy2ne : y ≠ (block505S2 : ℝ))
    (hy3ne : y ≠ (block505S3 : ℝ))
    (hy4ne : y ≠ (block505S4 : ℝ)) :
    0 < block505V y := by
  have hcert := block505RightChunk000Certificate_eq_true
  unfold block505RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block505RightChunk000) (lo := block505RightChunk000L) (hi := block505RightChunk000R)
    (w1 := block505W1) (w2 := block505W2) (w3 := block505W3) (w4 := block505W4)
    (s1 := block505S1) (s2 := block505S2) (s3 := block505S3) (s4 := block505S4)
    hboxes hcover block505RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block505_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block505RightL : ℝ) (block505RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block505S1 : ℝ))
    (hy2ne : y ≠ (block505S2 : ℝ))
    (hy3ne : y ≠ (block505S3 : ℝ))
    (hy4ne : y ≠ (block505S4 : ℝ)) :
    0 < block505V y := by
  have hL : (block505RightChunk000L : ℝ) = (block505RightL : ℝ) := by
    norm_num [block505RightChunk000L, block505RightL]
  have hR : (block505RightChunk000R : ℝ) = (block505RightR : ℝ) := by
    norm_num [block505RightChunk000R, block505RightR]
  have hyc : y ∈ Icc (block505RightChunk000L : ℝ) (block505RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block505_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block505_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block505LeftL : ℝ) (block505LeftR : ℝ) →
    y ≠ 0 → y ≠ (block505S1 : ℝ) → y ≠ (block505S2 : ℝ) →
    y ≠ (block505S3 : ℝ) → y ≠ (block505S4 : ℝ) → 0 < block505V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block505RightL : ℝ) (block505RightR : ℝ) →
    y ≠ 0 → y ≠ (block505S1 : ℝ) → y ≠ (block505S2 : ℝ) →
    y ≠ (block505S3 : ℝ) → y ≠ (block505S4 : ℝ) → 0 < block505V y)

theorem block505_reallog_certificate_proof :
    block505_reallog_certificate := by
  exact ⟨block505_left_V_pos, block505_right_V_pos⟩

end Block505
end M1817475
end Erdos1038Lean
