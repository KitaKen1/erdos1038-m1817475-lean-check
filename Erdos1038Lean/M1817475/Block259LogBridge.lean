import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block259

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block259

open Set

def block259W1 : Rat := ((1785268241121029 : Rat) / 2000000000000000)
def block259W2 : Rat := ((1874494275246803 : Rat) / 25000000000000000)
def block259W3 : Rat := ((19629653007833803 : Rat) / 100000000000000000)
def block259W4 : Rat := ((6228932114054367 : Rat) / 100000000000000000)
def block259S1 : Rat := ((18174751 : Rat) / 10000000)
def block259S2 : Rat := ((511587 : Rat) / 200000)
def block259S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block259S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block259V (y : ℝ) : ℝ :=
  ratPotential block259W1 block259W2 block259W3 block259W4 block259S1 block259S2 block259S3 block259S4 y

def block259LeftParamsCertificate : Bool :=
  allBoxesSameParams block259LeftBoxes block259W1 block259W2 block259W3 block259W4 block259S1 block259S2 block259S3 block259S4

theorem block259LeftParamsCertificate_eq_true :
    block259LeftParamsCertificate = true := by
  native_decide

theorem block259_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block259LeftL : ℝ) (block259LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block259S1 : ℝ))
    (hy2ne : y ≠ (block259S2 : ℝ))
    (hy3ne : y ≠ (block259S3 : ℝ))
    (hy4ne : y ≠ (block259S4 : ℝ)) :
    0 < block259V y := by
  have hcert := block259LeftCertificate_eq_true
  unfold block259LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block259LeftBoxes) (lo := block259LeftL) (hi := block259LeftR)
    (w1 := block259W1) (w2 := block259W2) (w3 := block259W3) (w4 := block259W4)
    (s1 := block259S1) (s2 := block259S2) (s3 := block259S3) (s4 := block259S4)
    hboxes hcover block259LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block259RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block259RightChunk000 block259W1 block259W2 block259W3 block259W4 block259S1 block259S2 block259S3 block259S4

theorem block259RightChunk000ParamsCertificate_eq_true :
    block259RightChunk000ParamsCertificate = true := by
  native_decide

theorem block259_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block259RightChunk000L : ℝ) (block259RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block259S1 : ℝ))
    (hy2ne : y ≠ (block259S2 : ℝ))
    (hy3ne : y ≠ (block259S3 : ℝ))
    (hy4ne : y ≠ (block259S4 : ℝ)) :
    0 < block259V y := by
  have hcert := block259RightChunk000Certificate_eq_true
  unfold block259RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block259RightChunk000) (lo := block259RightChunk000L) (hi := block259RightChunk000R)
    (w1 := block259W1) (w2 := block259W2) (w3 := block259W3) (w4 := block259W4)
    (s1 := block259S1) (s2 := block259S2) (s3 := block259S3) (s4 := block259S4)
    hboxes hcover block259RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block259RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block259RightChunk001 block259W1 block259W2 block259W3 block259W4 block259S1 block259S2 block259S3 block259S4

theorem block259RightChunk001ParamsCertificate_eq_true :
    block259RightChunk001ParamsCertificate = true := by
  native_decide

theorem block259_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block259RightChunk001L : ℝ) (block259RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block259S1 : ℝ))
    (hy2ne : y ≠ (block259S2 : ℝ))
    (hy3ne : y ≠ (block259S3 : ℝ))
    (hy4ne : y ≠ (block259S4 : ℝ)) :
    0 < block259V y := by
  have hcert := block259RightChunk001Certificate_eq_true
  unfold block259RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block259RightChunk001) (lo := block259RightChunk001L) (hi := block259RightChunk001R)
    (w1 := block259W1) (w2 := block259W2) (w3 := block259W3) (w4 := block259W4)
    (s1 := block259S1) (s2 := block259S2) (s3 := block259S3) (s4 := block259S4)
    hboxes hcover block259RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block259_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block259RightL : ℝ) (block259RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block259S1 : ℝ))
    (hy2ne : y ≠ (block259S2 : ℝ))
    (hy3ne : y ≠ (block259S3 : ℝ))
    (hy4ne : y ≠ (block259S4 : ℝ)) :
    0 < block259V y := by
  by_cases h0 : y ≤ (block259RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block259RightChunk000L : ℝ) (block259RightChunk000R : ℝ) := by
      have hL : (block259RightChunk000L : ℝ) = (block259RightL : ℝ) := by
        norm_num [block259RightChunk000L, block259RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block259_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block259RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block259RightChunk001L : ℝ) = (block259RightChunk000R : ℝ) := by
      norm_num [block259RightChunk001L, block259RightChunk000R]
    have hR : (block259RightChunk001R : ℝ) = (block259RightR : ℝ) := by
      norm_num [block259RightChunk001R, block259RightR]
    have hyc : y ∈ Icc (block259RightChunk001L : ℝ) (block259RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block259_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block259_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block259LeftL : ℝ) (block259LeftR : ℝ) →
    y ≠ 0 → y ≠ (block259S1 : ℝ) → y ≠ (block259S2 : ℝ) →
    y ≠ (block259S3 : ℝ) → y ≠ (block259S4 : ℝ) → 0 < block259V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block259RightL : ℝ) (block259RightR : ℝ) →
    y ≠ 0 → y ≠ (block259S1 : ℝ) → y ≠ (block259S2 : ℝ) →
    y ≠ (block259S3 : ℝ) → y ≠ (block259S4 : ℝ) → 0 < block259V y)

theorem block259_reallog_certificate_proof :
    block259_reallog_certificate := by
  exact ⟨block259_left_V_pos, block259_right_V_pos⟩

end Block259
end M1817475
end Erdos1038Lean
