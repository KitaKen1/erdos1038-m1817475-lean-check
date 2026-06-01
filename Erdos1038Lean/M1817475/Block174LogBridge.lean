import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block174

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block174

open Set

def block174W1 : Rat := ((18086330405470201 : Rat) / 10000000000000000)
def block174W2 : Rat := (0 : Rat)
def block174W3 : Rat := ((8503927101404639 : Rat) / 50000000000000000)
def block174W4 : Rat := ((9949409340815091 : Rat) / 100000000000000000)
def block174S1 : Rat := ((18174751 : Rat) / 10000000)
def block174S2 : Rat := ((511587 : Rat) / 200000)
def block174S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block174S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block174V (y : ℝ) : ℝ :=
  ratPotential block174W1 block174W2 block174W3 block174W4 block174S1 block174S2 block174S3 block174S4 y

def block174LeftParamsCertificate : Bool :=
  allBoxesSameParams block174LeftBoxes block174W1 block174W2 block174W3 block174W4 block174S1 block174S2 block174S3 block174S4

theorem block174LeftParamsCertificate_eq_true :
    block174LeftParamsCertificate = true := by
  native_decide

theorem block174_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block174LeftL : ℝ) (block174LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block174S1 : ℝ))
    (hy2ne : y ≠ (block174S2 : ℝ))
    (hy3ne : y ≠ (block174S3 : ℝ))
    (hy4ne : y ≠ (block174S4 : ℝ)) :
    0 < block174V y := by
  have hcert := block174LeftCertificate_eq_true
  unfold block174LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block174LeftBoxes) (lo := block174LeftL) (hi := block174LeftR)
    (w1 := block174W1) (w2 := block174W2) (w3 := block174W3) (w4 := block174W4)
    (s1 := block174S1) (s2 := block174S2) (s3 := block174S3) (s4 := block174S4)
    hboxes hcover block174LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block174RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block174RightChunk000 block174W1 block174W2 block174W3 block174W4 block174S1 block174S2 block174S3 block174S4

theorem block174RightChunk000ParamsCertificate_eq_true :
    block174RightChunk000ParamsCertificate = true := by
  native_decide

theorem block174_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block174RightChunk000L : ℝ) (block174RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block174S1 : ℝ))
    (hy2ne : y ≠ (block174S2 : ℝ))
    (hy3ne : y ≠ (block174S3 : ℝ))
    (hy4ne : y ≠ (block174S4 : ℝ)) :
    0 < block174V y := by
  have hcert := block174RightChunk000Certificate_eq_true
  unfold block174RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block174RightChunk000) (lo := block174RightChunk000L) (hi := block174RightChunk000R)
    (w1 := block174W1) (w2 := block174W2) (w3 := block174W3) (w4 := block174W4)
    (s1 := block174S1) (s2 := block174S2) (s3 := block174S3) (s4 := block174S4)
    hboxes hcover block174RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block174RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block174RightChunk001 block174W1 block174W2 block174W3 block174W4 block174S1 block174S2 block174S3 block174S4

theorem block174RightChunk001ParamsCertificate_eq_true :
    block174RightChunk001ParamsCertificate = true := by
  native_decide

theorem block174_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block174RightChunk001L : ℝ) (block174RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block174S1 : ℝ))
    (hy2ne : y ≠ (block174S2 : ℝ))
    (hy3ne : y ≠ (block174S3 : ℝ))
    (hy4ne : y ≠ (block174S4 : ℝ)) :
    0 < block174V y := by
  have hcert := block174RightChunk001Certificate_eq_true
  unfold block174RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block174RightChunk001) (lo := block174RightChunk001L) (hi := block174RightChunk001R)
    (w1 := block174W1) (w2 := block174W2) (w3 := block174W3) (w4 := block174W4)
    (s1 := block174S1) (s2 := block174S2) (s3 := block174S3) (s4 := block174S4)
    hboxes hcover block174RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block174_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block174RightL : ℝ) (block174RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block174S1 : ℝ))
    (hy2ne : y ≠ (block174S2 : ℝ))
    (hy3ne : y ≠ (block174S3 : ℝ))
    (hy4ne : y ≠ (block174S4 : ℝ)) :
    0 < block174V y := by
  by_cases h0 : y ≤ (block174RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block174RightChunk000L : ℝ) (block174RightChunk000R : ℝ) := by
      have hL : (block174RightChunk000L : ℝ) = (block174RightL : ℝ) := by
        norm_num [block174RightChunk000L, block174RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block174_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block174RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block174RightChunk001L : ℝ) = (block174RightChunk000R : ℝ) := by
      norm_num [block174RightChunk001L, block174RightChunk000R]
    have hR : (block174RightChunk001R : ℝ) = (block174RightR : ℝ) := by
      norm_num [block174RightChunk001R, block174RightR]
    have hyc : y ∈ Icc (block174RightChunk001L : ℝ) (block174RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block174_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block174_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block174LeftL : ℝ) (block174LeftR : ℝ) →
    y ≠ 0 → y ≠ (block174S1 : ℝ) → y ≠ (block174S2 : ℝ) →
    y ≠ (block174S3 : ℝ) → y ≠ (block174S4 : ℝ) → 0 < block174V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block174RightL : ℝ) (block174RightR : ℝ) →
    y ≠ 0 → y ≠ (block174S1 : ℝ) → y ≠ (block174S2 : ℝ) →
    y ≠ (block174S3 : ℝ) → y ≠ (block174S4 : ℝ) → 0 < block174V y)

theorem block174_reallog_certificate_proof :
    block174_reallog_certificate := by
  exact ⟨block174_left_V_pos, block174_right_V_pos⟩

end Block174
end M1817475
end Erdos1038Lean
