import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block183

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block183

open Set

def block183W1 : Rat := ((8882877186726661 : Rat) / 5000000000000000)
def block183W2 : Rat := (0 : Rat)
def block183W3 : Rat := ((1753592379759851 : Rat) / 10000000000000000)
def block183W4 : Rat := ((9575463312445491 : Rat) / 100000000000000000)
def block183S1 : Rat := ((18174751 : Rat) / 10000000)
def block183S2 : Rat := ((511587 : Rat) / 200000)
def block183S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block183S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block183V (y : ℝ) : ℝ :=
  ratPotential block183W1 block183W2 block183W3 block183W4 block183S1 block183S2 block183S3 block183S4 y

def block183LeftParamsCertificate : Bool :=
  allBoxesSameParams block183LeftBoxes block183W1 block183W2 block183W3 block183W4 block183S1 block183S2 block183S3 block183S4

theorem block183LeftParamsCertificate_eq_true :
    block183LeftParamsCertificate = true := by
  native_decide

theorem block183_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block183LeftL : ℝ) (block183LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block183S1 : ℝ))
    (hy2ne : y ≠ (block183S2 : ℝ))
    (hy3ne : y ≠ (block183S3 : ℝ))
    (hy4ne : y ≠ (block183S4 : ℝ)) :
    0 < block183V y := by
  have hcert := block183LeftCertificate_eq_true
  unfold block183LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block183LeftBoxes) (lo := block183LeftL) (hi := block183LeftR)
    (w1 := block183W1) (w2 := block183W2) (w3 := block183W3) (w4 := block183W4)
    (s1 := block183S1) (s2 := block183S2) (s3 := block183S3) (s4 := block183S4)
    hboxes hcover block183LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block183RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block183RightChunk000 block183W1 block183W2 block183W3 block183W4 block183S1 block183S2 block183S3 block183S4

theorem block183RightChunk000ParamsCertificate_eq_true :
    block183RightChunk000ParamsCertificate = true := by
  native_decide

theorem block183_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block183RightChunk000L : ℝ) (block183RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block183S1 : ℝ))
    (hy2ne : y ≠ (block183S2 : ℝ))
    (hy3ne : y ≠ (block183S3 : ℝ))
    (hy4ne : y ≠ (block183S4 : ℝ)) :
    0 < block183V y := by
  have hcert := block183RightChunk000Certificate_eq_true
  unfold block183RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block183RightChunk000) (lo := block183RightChunk000L) (hi := block183RightChunk000R)
    (w1 := block183W1) (w2 := block183W2) (w3 := block183W3) (w4 := block183W4)
    (s1 := block183S1) (s2 := block183S2) (s3 := block183S3) (s4 := block183S4)
    hboxes hcover block183RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block183RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block183RightChunk001 block183W1 block183W2 block183W3 block183W4 block183S1 block183S2 block183S3 block183S4

theorem block183RightChunk001ParamsCertificate_eq_true :
    block183RightChunk001ParamsCertificate = true := by
  native_decide

theorem block183_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block183RightChunk001L : ℝ) (block183RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block183S1 : ℝ))
    (hy2ne : y ≠ (block183S2 : ℝ))
    (hy3ne : y ≠ (block183S3 : ℝ))
    (hy4ne : y ≠ (block183S4 : ℝ)) :
    0 < block183V y := by
  have hcert := block183RightChunk001Certificate_eq_true
  unfold block183RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block183RightChunk001) (lo := block183RightChunk001L) (hi := block183RightChunk001R)
    (w1 := block183W1) (w2 := block183W2) (w3 := block183W3) (w4 := block183W4)
    (s1 := block183S1) (s2 := block183S2) (s3 := block183S3) (s4 := block183S4)
    hboxes hcover block183RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block183_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block183RightL : ℝ) (block183RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block183S1 : ℝ))
    (hy2ne : y ≠ (block183S2 : ℝ))
    (hy3ne : y ≠ (block183S3 : ℝ))
    (hy4ne : y ≠ (block183S4 : ℝ)) :
    0 < block183V y := by
  by_cases h0 : y ≤ (block183RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block183RightChunk000L : ℝ) (block183RightChunk000R : ℝ) := by
      have hL : (block183RightChunk000L : ℝ) = (block183RightL : ℝ) := by
        norm_num [block183RightChunk000L, block183RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block183_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block183RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block183RightChunk001L : ℝ) = (block183RightChunk000R : ℝ) := by
      norm_num [block183RightChunk001L, block183RightChunk000R]
    have hR : (block183RightChunk001R : ℝ) = (block183RightR : ℝ) := by
      norm_num [block183RightChunk001R, block183RightR]
    have hyc : y ∈ Icc (block183RightChunk001L : ℝ) (block183RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block183_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block183_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block183LeftL : ℝ) (block183LeftR : ℝ) →
    y ≠ 0 → y ≠ (block183S1 : ℝ) → y ≠ (block183S2 : ℝ) →
    y ≠ (block183S3 : ℝ) → y ≠ (block183S4 : ℝ) → 0 < block183V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block183RightL : ℝ) (block183RightR : ℝ) →
    y ≠ 0 → y ≠ (block183S1 : ℝ) → y ≠ (block183S2 : ℝ) →
    y ≠ (block183S3 : ℝ) → y ≠ (block183S4 : ℝ) → 0 < block183V y)

theorem block183_reallog_certificate_proof :
    block183_reallog_certificate := by
  exact ⟨block183_left_V_pos, block183_right_V_pos⟩

end Block183
end M1817475
end Erdos1038Lean
