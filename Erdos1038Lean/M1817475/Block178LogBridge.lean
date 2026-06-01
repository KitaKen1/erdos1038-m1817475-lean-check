import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block178

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block178

open Set

def block178W1 : Rat := ((896944818900707 : Rat) / 500000000000000)
def block178W2 : Rat := (0 : Rat)
def block178W3 : Rat := ((8624953731371919 : Rat) / 50000000000000000)
def block178W4 : Rat := ((4888770839424123 : Rat) / 50000000000000000)
def block178S1 : Rat := ((18174751 : Rat) / 10000000)
def block178S2 : Rat := ((511587 : Rat) / 200000)
def block178S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block178S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block178V (y : ℝ) : ℝ :=
  ratPotential block178W1 block178W2 block178W3 block178W4 block178S1 block178S2 block178S3 block178S4 y

def block178LeftParamsCertificate : Bool :=
  allBoxesSameParams block178LeftBoxes block178W1 block178W2 block178W3 block178W4 block178S1 block178S2 block178S3 block178S4

theorem block178LeftParamsCertificate_eq_true :
    block178LeftParamsCertificate = true := by
  native_decide

theorem block178_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block178LeftL : ℝ) (block178LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block178S1 : ℝ))
    (hy2ne : y ≠ (block178S2 : ℝ))
    (hy3ne : y ≠ (block178S3 : ℝ))
    (hy4ne : y ≠ (block178S4 : ℝ)) :
    0 < block178V y := by
  have hcert := block178LeftCertificate_eq_true
  unfold block178LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block178LeftBoxes) (lo := block178LeftL) (hi := block178LeftR)
    (w1 := block178W1) (w2 := block178W2) (w3 := block178W3) (w4 := block178W4)
    (s1 := block178S1) (s2 := block178S2) (s3 := block178S3) (s4 := block178S4)
    hboxes hcover block178LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block178RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block178RightChunk000 block178W1 block178W2 block178W3 block178W4 block178S1 block178S2 block178S3 block178S4

theorem block178RightChunk000ParamsCertificate_eq_true :
    block178RightChunk000ParamsCertificate = true := by
  native_decide

theorem block178_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block178RightChunk000L : ℝ) (block178RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block178S1 : ℝ))
    (hy2ne : y ≠ (block178S2 : ℝ))
    (hy3ne : y ≠ (block178S3 : ℝ))
    (hy4ne : y ≠ (block178S4 : ℝ)) :
    0 < block178V y := by
  have hcert := block178RightChunk000Certificate_eq_true
  unfold block178RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block178RightChunk000) (lo := block178RightChunk000L) (hi := block178RightChunk000R)
    (w1 := block178W1) (w2 := block178W2) (w3 := block178W3) (w4 := block178W4)
    (s1 := block178S1) (s2 := block178S2) (s3 := block178S3) (s4 := block178S4)
    hboxes hcover block178RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block178RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block178RightChunk001 block178W1 block178W2 block178W3 block178W4 block178S1 block178S2 block178S3 block178S4

theorem block178RightChunk001ParamsCertificate_eq_true :
    block178RightChunk001ParamsCertificate = true := by
  native_decide

theorem block178_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block178RightChunk001L : ℝ) (block178RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block178S1 : ℝ))
    (hy2ne : y ≠ (block178S2 : ℝ))
    (hy3ne : y ≠ (block178S3 : ℝ))
    (hy4ne : y ≠ (block178S4 : ℝ)) :
    0 < block178V y := by
  have hcert := block178RightChunk001Certificate_eq_true
  unfold block178RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block178RightChunk001) (lo := block178RightChunk001L) (hi := block178RightChunk001R)
    (w1 := block178W1) (w2 := block178W2) (w3 := block178W3) (w4 := block178W4)
    (s1 := block178S1) (s2 := block178S2) (s3 := block178S3) (s4 := block178S4)
    hboxes hcover block178RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block178_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block178RightL : ℝ) (block178RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block178S1 : ℝ))
    (hy2ne : y ≠ (block178S2 : ℝ))
    (hy3ne : y ≠ (block178S3 : ℝ))
    (hy4ne : y ≠ (block178S4 : ℝ)) :
    0 < block178V y := by
  by_cases h0 : y ≤ (block178RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block178RightChunk000L : ℝ) (block178RightChunk000R : ℝ) := by
      have hL : (block178RightChunk000L : ℝ) = (block178RightL : ℝ) := by
        norm_num [block178RightChunk000L, block178RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block178_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block178RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block178RightChunk001L : ℝ) = (block178RightChunk000R : ℝ) := by
      norm_num [block178RightChunk001L, block178RightChunk000R]
    have hR : (block178RightChunk001R : ℝ) = (block178RightR : ℝ) := by
      norm_num [block178RightChunk001R, block178RightR]
    have hyc : y ∈ Icc (block178RightChunk001L : ℝ) (block178RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block178_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block178_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block178LeftL : ℝ) (block178LeftR : ℝ) →
    y ≠ 0 → y ≠ (block178S1 : ℝ) → y ≠ (block178S2 : ℝ) →
    y ≠ (block178S3 : ℝ) → y ≠ (block178S4 : ℝ) → 0 < block178V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block178RightL : ℝ) (block178RightR : ℝ) →
    y ≠ 0 → y ≠ (block178S1 : ℝ) → y ≠ (block178S2 : ℝ) →
    y ≠ (block178S3 : ℝ) → y ≠ (block178S4 : ℝ) → 0 < block178V y)

theorem block178_reallog_certificate_proof :
    block178_reallog_certificate := by
  exact ⟨block178_left_V_pos, block178_right_V_pos⟩

end Block178
end M1817475
end Erdos1038Lean
