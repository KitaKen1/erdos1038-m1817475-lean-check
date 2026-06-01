import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block268

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block268

open Set

def block268W1 : Rat := ((2570869131350959 : Rat) / 2500000000000000)
def block268W2 : Rat := ((5663899632095297 : Rat) / 200000000000000000)
def block268W3 : Rat := ((2943081186261129 : Rat) / 10000000000000000)
def block268W4 : Rat := (0 : Rat)
def block268S1 : Rat := ((18174751 : Rat) / 10000000)
def block268S2 : Rat := ((511587 : Rat) / 200000)
def block268S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block268S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block268V (y : ℝ) : ℝ :=
  ratPotential block268W1 block268W2 block268W3 block268W4 block268S1 block268S2 block268S3 block268S4 y

def block268LeftParamsCertificate : Bool :=
  allBoxesSameParams block268LeftBoxes block268W1 block268W2 block268W3 block268W4 block268S1 block268S2 block268S3 block268S4

theorem block268LeftParamsCertificate_eq_true :
    block268LeftParamsCertificate = true := by
  native_decide

theorem block268_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block268LeftL : ℝ) (block268LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block268S1 : ℝ))
    (hy2ne : y ≠ (block268S2 : ℝ))
    (hy3ne : y ≠ (block268S3 : ℝ))
    (hy4ne : y ≠ (block268S4 : ℝ)) :
    0 < block268V y := by
  have hcert := block268LeftCertificate_eq_true
  unfold block268LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block268LeftBoxes) (lo := block268LeftL) (hi := block268LeftR)
    (w1 := block268W1) (w2 := block268W2) (w3 := block268W3) (w4 := block268W4)
    (s1 := block268S1) (s2 := block268S2) (s3 := block268S3) (s4 := block268S4)
    hboxes hcover block268LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block268RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block268RightChunk000 block268W1 block268W2 block268W3 block268W4 block268S1 block268S2 block268S3 block268S4

theorem block268RightChunk000ParamsCertificate_eq_true :
    block268RightChunk000ParamsCertificate = true := by
  native_decide

theorem block268_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block268RightChunk000L : ℝ) (block268RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block268S1 : ℝ))
    (hy2ne : y ≠ (block268S2 : ℝ))
    (hy3ne : y ≠ (block268S3 : ℝ))
    (hy4ne : y ≠ (block268S4 : ℝ)) :
    0 < block268V y := by
  have hcert := block268RightChunk000Certificate_eq_true
  unfold block268RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block268RightChunk000) (lo := block268RightChunk000L) (hi := block268RightChunk000R)
    (w1 := block268W1) (w2 := block268W2) (w3 := block268W3) (w4 := block268W4)
    (s1 := block268S1) (s2 := block268S2) (s3 := block268S3) (s4 := block268S4)
    hboxes hcover block268RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block268RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block268RightChunk001 block268W1 block268W2 block268W3 block268W4 block268S1 block268S2 block268S3 block268S4

theorem block268RightChunk001ParamsCertificate_eq_true :
    block268RightChunk001ParamsCertificate = true := by
  native_decide

theorem block268_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block268RightChunk001L : ℝ) (block268RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block268S1 : ℝ))
    (hy2ne : y ≠ (block268S2 : ℝ))
    (hy3ne : y ≠ (block268S3 : ℝ))
    (hy4ne : y ≠ (block268S4 : ℝ)) :
    0 < block268V y := by
  have hcert := block268RightChunk001Certificate_eq_true
  unfold block268RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block268RightChunk001) (lo := block268RightChunk001L) (hi := block268RightChunk001R)
    (w1 := block268W1) (w2 := block268W2) (w3 := block268W3) (w4 := block268W4)
    (s1 := block268S1) (s2 := block268S2) (s3 := block268S3) (s4 := block268S4)
    hboxes hcover block268RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block268_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block268RightL : ℝ) (block268RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block268S1 : ℝ))
    (hy2ne : y ≠ (block268S2 : ℝ))
    (hy3ne : y ≠ (block268S3 : ℝ))
    (hy4ne : y ≠ (block268S4 : ℝ)) :
    0 < block268V y := by
  by_cases h0 : y ≤ (block268RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block268RightChunk000L : ℝ) (block268RightChunk000R : ℝ) := by
      have hL : (block268RightChunk000L : ℝ) = (block268RightL : ℝ) := by
        norm_num [block268RightChunk000L, block268RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block268_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block268RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block268RightChunk001L : ℝ) = (block268RightChunk000R : ℝ) := by
      norm_num [block268RightChunk001L, block268RightChunk000R]
    have hR : (block268RightChunk001R : ℝ) = (block268RightR : ℝ) := by
      norm_num [block268RightChunk001R, block268RightR]
    have hyc : y ∈ Icc (block268RightChunk001L : ℝ) (block268RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block268_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block268_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block268LeftL : ℝ) (block268LeftR : ℝ) →
    y ≠ 0 → y ≠ (block268S1 : ℝ) → y ≠ (block268S2 : ℝ) →
    y ≠ (block268S3 : ℝ) → y ≠ (block268S4 : ℝ) → 0 < block268V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block268RightL : ℝ) (block268RightR : ℝ) →
    y ≠ 0 → y ≠ (block268S1 : ℝ) → y ≠ (block268S2 : ℝ) →
    y ≠ (block268S3 : ℝ) → y ≠ (block268S4 : ℝ) → 0 < block268V y)

theorem block268_reallog_certificate_proof :
    block268_reallog_certificate := by
  exact ⟨block268_left_V_pos, block268_right_V_pos⟩

end Block268
end M1817475
end Erdos1038Lean
