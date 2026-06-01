import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block262

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block262

open Set

def block262W1 : Rat := ((8984027938798961 : Rat) / 10000000000000000)
def block262W2 : Rat := ((1831059357642667 : Rat) / 25000000000000000)
def block262W3 : Rat := ((4989145111655751 : Rat) / 25000000000000000)
def block262W4 : Rat := ((6006731754926947 : Rat) / 100000000000000000)
def block262S1 : Rat := ((18174751 : Rat) / 10000000)
def block262S2 : Rat := ((511587 : Rat) / 200000)
def block262S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block262S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block262V (y : ℝ) : ℝ :=
  ratPotential block262W1 block262W2 block262W3 block262W4 block262S1 block262S2 block262S3 block262S4 y

def block262LeftParamsCertificate : Bool :=
  allBoxesSameParams block262LeftBoxes block262W1 block262W2 block262W3 block262W4 block262S1 block262S2 block262S3 block262S4

theorem block262LeftParamsCertificate_eq_true :
    block262LeftParamsCertificate = true := by
  native_decide

theorem block262_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block262LeftL : ℝ) (block262LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block262S1 : ℝ))
    (hy2ne : y ≠ (block262S2 : ℝ))
    (hy3ne : y ≠ (block262S3 : ℝ))
    (hy4ne : y ≠ (block262S4 : ℝ)) :
    0 < block262V y := by
  have hcert := block262LeftCertificate_eq_true
  unfold block262LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block262LeftBoxes) (lo := block262LeftL) (hi := block262LeftR)
    (w1 := block262W1) (w2 := block262W2) (w3 := block262W3) (w4 := block262W4)
    (s1 := block262S1) (s2 := block262S2) (s3 := block262S3) (s4 := block262S4)
    hboxes hcover block262LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block262RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block262RightChunk000 block262W1 block262W2 block262W3 block262W4 block262S1 block262S2 block262S3 block262S4

theorem block262RightChunk000ParamsCertificate_eq_true :
    block262RightChunk000ParamsCertificate = true := by
  native_decide

theorem block262_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block262RightChunk000L : ℝ) (block262RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block262S1 : ℝ))
    (hy2ne : y ≠ (block262S2 : ℝ))
    (hy3ne : y ≠ (block262S3 : ℝ))
    (hy4ne : y ≠ (block262S4 : ℝ)) :
    0 < block262V y := by
  have hcert := block262RightChunk000Certificate_eq_true
  unfold block262RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block262RightChunk000) (lo := block262RightChunk000L) (hi := block262RightChunk000R)
    (w1 := block262W1) (w2 := block262W2) (w3 := block262W3) (w4 := block262W4)
    (s1 := block262S1) (s2 := block262S2) (s3 := block262S3) (s4 := block262S4)
    hboxes hcover block262RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block262RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block262RightChunk001 block262W1 block262W2 block262W3 block262W4 block262S1 block262S2 block262S3 block262S4

theorem block262RightChunk001ParamsCertificate_eq_true :
    block262RightChunk001ParamsCertificate = true := by
  native_decide

theorem block262_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block262RightChunk001L : ℝ) (block262RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block262S1 : ℝ))
    (hy2ne : y ≠ (block262S2 : ℝ))
    (hy3ne : y ≠ (block262S3 : ℝ))
    (hy4ne : y ≠ (block262S4 : ℝ)) :
    0 < block262V y := by
  have hcert := block262RightChunk001Certificate_eq_true
  unfold block262RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block262RightChunk001) (lo := block262RightChunk001L) (hi := block262RightChunk001R)
    (w1 := block262W1) (w2 := block262W2) (w3 := block262W3) (w4 := block262W4)
    (s1 := block262S1) (s2 := block262S2) (s3 := block262S3) (s4 := block262S4)
    hboxes hcover block262RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block262_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block262RightL : ℝ) (block262RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block262S1 : ℝ))
    (hy2ne : y ≠ (block262S2 : ℝ))
    (hy3ne : y ≠ (block262S3 : ℝ))
    (hy4ne : y ≠ (block262S4 : ℝ)) :
    0 < block262V y := by
  by_cases h0 : y ≤ (block262RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block262RightChunk000L : ℝ) (block262RightChunk000R : ℝ) := by
      have hL : (block262RightChunk000L : ℝ) = (block262RightL : ℝ) := by
        norm_num [block262RightChunk000L, block262RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block262_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block262RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block262RightChunk001L : ℝ) = (block262RightChunk000R : ℝ) := by
      norm_num [block262RightChunk001L, block262RightChunk000R]
    have hR : (block262RightChunk001R : ℝ) = (block262RightR : ℝ) := by
      norm_num [block262RightChunk001R, block262RightR]
    have hyc : y ∈ Icc (block262RightChunk001L : ℝ) (block262RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block262_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block262_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block262LeftL : ℝ) (block262LeftR : ℝ) →
    y ≠ 0 → y ≠ (block262S1 : ℝ) → y ≠ (block262S2 : ℝ) →
    y ≠ (block262S3 : ℝ) → y ≠ (block262S4 : ℝ) → 0 < block262V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block262RightL : ℝ) (block262RightR : ℝ) →
    y ≠ 0 → y ≠ (block262S1 : ℝ) → y ≠ (block262S2 : ℝ) →
    y ≠ (block262S3 : ℝ) → y ≠ (block262S4 : ℝ) → 0 < block262V y)

theorem block262_reallog_certificate_proof :
    block262_reallog_certificate := by
  exact ⟨block262_left_V_pos, block262_right_V_pos⟩

end Block262
end M1817475
end Erdos1038Lean
