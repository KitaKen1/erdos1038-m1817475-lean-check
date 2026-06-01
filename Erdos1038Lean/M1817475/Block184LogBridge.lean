import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block184

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block184

open Set

def block184W1 : Rat := ((27695272975207 : Rat) / 15625000000000)
def block184W2 : Rat := (0 : Rat)
def block184W3 : Rat := ((17604658487539201 : Rat) / 100000000000000000)
def block184W4 : Rat := ((9527518544902479 : Rat) / 100000000000000000)
def block184S1 : Rat := ((18174751 : Rat) / 10000000)
def block184S2 : Rat := ((511587 : Rat) / 200000)
def block184S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block184S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block184V (y : ℝ) : ℝ :=
  ratPotential block184W1 block184W2 block184W3 block184W4 block184S1 block184S2 block184S3 block184S4 y

def block184LeftParamsCertificate : Bool :=
  allBoxesSameParams block184LeftBoxes block184W1 block184W2 block184W3 block184W4 block184S1 block184S2 block184S3 block184S4

theorem block184LeftParamsCertificate_eq_true :
    block184LeftParamsCertificate = true := by
  native_decide

theorem block184_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block184LeftL : ℝ) (block184LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block184S1 : ℝ))
    (hy2ne : y ≠ (block184S2 : ℝ))
    (hy3ne : y ≠ (block184S3 : ℝ))
    (hy4ne : y ≠ (block184S4 : ℝ)) :
    0 < block184V y := by
  have hcert := block184LeftCertificate_eq_true
  unfold block184LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block184LeftBoxes) (lo := block184LeftL) (hi := block184LeftR)
    (w1 := block184W1) (w2 := block184W2) (w3 := block184W3) (w4 := block184W4)
    (s1 := block184S1) (s2 := block184S2) (s3 := block184S3) (s4 := block184S4)
    hboxes hcover block184LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block184RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block184RightChunk000 block184W1 block184W2 block184W3 block184W4 block184S1 block184S2 block184S3 block184S4

theorem block184RightChunk000ParamsCertificate_eq_true :
    block184RightChunk000ParamsCertificate = true := by
  native_decide

theorem block184_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block184RightChunk000L : ℝ) (block184RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block184S1 : ℝ))
    (hy2ne : y ≠ (block184S2 : ℝ))
    (hy3ne : y ≠ (block184S3 : ℝ))
    (hy4ne : y ≠ (block184S4 : ℝ)) :
    0 < block184V y := by
  have hcert := block184RightChunk000Certificate_eq_true
  unfold block184RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block184RightChunk000) (lo := block184RightChunk000L) (hi := block184RightChunk000R)
    (w1 := block184W1) (w2 := block184W2) (w3 := block184W3) (w4 := block184W4)
    (s1 := block184S1) (s2 := block184S2) (s3 := block184S3) (s4 := block184S4)
    hboxes hcover block184RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block184RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block184RightChunk001 block184W1 block184W2 block184W3 block184W4 block184S1 block184S2 block184S3 block184S4

theorem block184RightChunk001ParamsCertificate_eq_true :
    block184RightChunk001ParamsCertificate = true := by
  native_decide

theorem block184_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block184RightChunk001L : ℝ) (block184RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block184S1 : ℝ))
    (hy2ne : y ≠ (block184S2 : ℝ))
    (hy3ne : y ≠ (block184S3 : ℝ))
    (hy4ne : y ≠ (block184S4 : ℝ)) :
    0 < block184V y := by
  have hcert := block184RightChunk001Certificate_eq_true
  unfold block184RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block184RightChunk001) (lo := block184RightChunk001L) (hi := block184RightChunk001R)
    (w1 := block184W1) (w2 := block184W2) (w3 := block184W3) (w4 := block184W4)
    (s1 := block184S1) (s2 := block184S2) (s3 := block184S3) (s4 := block184S4)
    hboxes hcover block184RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block184_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block184RightL : ℝ) (block184RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block184S1 : ℝ))
    (hy2ne : y ≠ (block184S2 : ℝ))
    (hy3ne : y ≠ (block184S3 : ℝ))
    (hy4ne : y ≠ (block184S4 : ℝ)) :
    0 < block184V y := by
  by_cases h0 : y ≤ (block184RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block184RightChunk000L : ℝ) (block184RightChunk000R : ℝ) := by
      have hL : (block184RightChunk000L : ℝ) = (block184RightL : ℝ) := by
        norm_num [block184RightChunk000L, block184RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block184_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block184RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block184RightChunk001L : ℝ) = (block184RightChunk000R : ℝ) := by
      norm_num [block184RightChunk001L, block184RightChunk000R]
    have hR : (block184RightChunk001R : ℝ) = (block184RightR : ℝ) := by
      norm_num [block184RightChunk001R, block184RightR]
    have hyc : y ∈ Icc (block184RightChunk001L : ℝ) (block184RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block184_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block184_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block184LeftL : ℝ) (block184LeftR : ℝ) →
    y ≠ 0 → y ≠ (block184S1 : ℝ) → y ≠ (block184S2 : ℝ) →
    y ≠ (block184S3 : ℝ) → y ≠ (block184S4 : ℝ) → 0 < block184V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block184RightL : ℝ) (block184RightR : ℝ) →
    y ≠ 0 → y ≠ (block184S1 : ℝ) → y ≠ (block184S2 : ℝ) →
    y ≠ (block184S3 : ℝ) → y ≠ (block184S4 : ℝ) → 0 < block184V y)

theorem block184_reallog_certificate_proof :
    block184_reallog_certificate := by
  exact ⟨block184_left_V_pos, block184_right_V_pos⟩

end Block184
end M1817475
end Erdos1038Lean
