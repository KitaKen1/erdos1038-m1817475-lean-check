import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block188

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block188

open Set

def block188W1 : Rat := ((70355982449313 : Rat) / 40000000000000)
def block188W2 : Rat := (0 : Rat)
def block188W3 : Rat := ((8916054746769751 : Rat) / 50000000000000000)
def block188W4 : Rat := ((9368266191907637 : Rat) / 100000000000000000)
def block188S1 : Rat := ((18174751 : Rat) / 10000000)
def block188S2 : Rat := ((511587 : Rat) / 200000)
def block188S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block188S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block188V (y : ℝ) : ℝ :=
  ratPotential block188W1 block188W2 block188W3 block188W4 block188S1 block188S2 block188S3 block188S4 y

def block188LeftParamsCertificate : Bool :=
  allBoxesSameParams block188LeftBoxes block188W1 block188W2 block188W3 block188W4 block188S1 block188S2 block188S3 block188S4

theorem block188LeftParamsCertificate_eq_true :
    block188LeftParamsCertificate = true := by
  native_decide

theorem block188_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block188LeftL : ℝ) (block188LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block188S1 : ℝ))
    (hy2ne : y ≠ (block188S2 : ℝ))
    (hy3ne : y ≠ (block188S3 : ℝ))
    (hy4ne : y ≠ (block188S4 : ℝ)) :
    0 < block188V y := by
  have hcert := block188LeftCertificate_eq_true
  unfold block188LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block188LeftBoxes) (lo := block188LeftL) (hi := block188LeftR)
    (w1 := block188W1) (w2 := block188W2) (w3 := block188W3) (w4 := block188W4)
    (s1 := block188S1) (s2 := block188S2) (s3 := block188S3) (s4 := block188S4)
    hboxes hcover block188LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block188RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block188RightChunk000 block188W1 block188W2 block188W3 block188W4 block188S1 block188S2 block188S3 block188S4

theorem block188RightChunk000ParamsCertificate_eq_true :
    block188RightChunk000ParamsCertificate = true := by
  native_decide

theorem block188_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block188RightChunk000L : ℝ) (block188RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block188S1 : ℝ))
    (hy2ne : y ≠ (block188S2 : ℝ))
    (hy3ne : y ≠ (block188S3 : ℝ))
    (hy4ne : y ≠ (block188S4 : ℝ)) :
    0 < block188V y := by
  have hcert := block188RightChunk000Certificate_eq_true
  unfold block188RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block188RightChunk000) (lo := block188RightChunk000L) (hi := block188RightChunk000R)
    (w1 := block188W1) (w2 := block188W2) (w3 := block188W3) (w4 := block188W4)
    (s1 := block188S1) (s2 := block188S2) (s3 := block188S3) (s4 := block188S4)
    hboxes hcover block188RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block188RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block188RightChunk001 block188W1 block188W2 block188W3 block188W4 block188S1 block188S2 block188S3 block188S4

theorem block188RightChunk001ParamsCertificate_eq_true :
    block188RightChunk001ParamsCertificate = true := by
  native_decide

theorem block188_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block188RightChunk001L : ℝ) (block188RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block188S1 : ℝ))
    (hy2ne : y ≠ (block188S2 : ℝ))
    (hy3ne : y ≠ (block188S3 : ℝ))
    (hy4ne : y ≠ (block188S4 : ℝ)) :
    0 < block188V y := by
  have hcert := block188RightChunk001Certificate_eq_true
  unfold block188RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block188RightChunk001) (lo := block188RightChunk001L) (hi := block188RightChunk001R)
    (w1 := block188W1) (w2 := block188W2) (w3 := block188W3) (w4 := block188W4)
    (s1 := block188S1) (s2 := block188S2) (s3 := block188S3) (s4 := block188S4)
    hboxes hcover block188RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block188_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block188RightL : ℝ) (block188RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block188S1 : ℝ))
    (hy2ne : y ≠ (block188S2 : ℝ))
    (hy3ne : y ≠ (block188S3 : ℝ))
    (hy4ne : y ≠ (block188S4 : ℝ)) :
    0 < block188V y := by
  by_cases h0 : y ≤ (block188RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block188RightChunk000L : ℝ) (block188RightChunk000R : ℝ) := by
      have hL : (block188RightChunk000L : ℝ) = (block188RightL : ℝ) := by
        norm_num [block188RightChunk000L, block188RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block188_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block188RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block188RightChunk001L : ℝ) = (block188RightChunk000R : ℝ) := by
      norm_num [block188RightChunk001L, block188RightChunk000R]
    have hR : (block188RightChunk001R : ℝ) = (block188RightR : ℝ) := by
      norm_num [block188RightChunk001R, block188RightR]
    have hyc : y ∈ Icc (block188RightChunk001L : ℝ) (block188RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block188_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block188_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block188LeftL : ℝ) (block188LeftR : ℝ) →
    y ≠ 0 → y ≠ (block188S1 : ℝ) → y ≠ (block188S2 : ℝ) →
    y ≠ (block188S3 : ℝ) → y ≠ (block188S4 : ℝ) → 0 < block188V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block188RightL : ℝ) (block188RightR : ℝ) →
    y ≠ 0 → y ≠ (block188S1 : ℝ) → y ≠ (block188S2 : ℝ) →
    y ≠ (block188S3 : ℝ) → y ≠ (block188S4 : ℝ) → 0 < block188V y)

theorem block188_reallog_certificate_proof :
    block188_reallog_certificate := by
  exact ⟨block188_left_V_pos, block188_right_V_pos⟩

end Block188
end M1817475
end Erdos1038Lean
