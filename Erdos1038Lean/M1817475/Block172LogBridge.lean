import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block172

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block172

open Set

def block172W1 : Rat := ((18157055131371727 : Rat) / 10000000000000000)
def block172W2 : Rat := (0 : Rat)
def block172W3 : Rat := ((16893042516110107 : Rat) / 100000000000000000)
def block172W4 : Rat := ((10031548731137031 : Rat) / 100000000000000000)
def block172S1 : Rat := ((18174751 : Rat) / 10000000)
def block172S2 : Rat := ((511587 : Rat) / 200000)
def block172S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block172S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block172V (y : ℝ) : ℝ :=
  ratPotential block172W1 block172W2 block172W3 block172W4 block172S1 block172S2 block172S3 block172S4 y

def block172LeftParamsCertificate : Bool :=
  allBoxesSameParams block172LeftBoxes block172W1 block172W2 block172W3 block172W4 block172S1 block172S2 block172S3 block172S4

theorem block172LeftParamsCertificate_eq_true :
    block172LeftParamsCertificate = true := by
  native_decide

theorem block172_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block172LeftL : ℝ) (block172LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block172S1 : ℝ))
    (hy2ne : y ≠ (block172S2 : ℝ))
    (hy3ne : y ≠ (block172S3 : ℝ))
    (hy4ne : y ≠ (block172S4 : ℝ)) :
    0 < block172V y := by
  have hcert := block172LeftCertificate_eq_true
  unfold block172LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block172LeftBoxes) (lo := block172LeftL) (hi := block172LeftR)
    (w1 := block172W1) (w2 := block172W2) (w3 := block172W3) (w4 := block172W4)
    (s1 := block172S1) (s2 := block172S2) (s3 := block172S3) (s4 := block172S4)
    hboxes hcover block172LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block172RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block172RightChunk000 block172W1 block172W2 block172W3 block172W4 block172S1 block172S2 block172S3 block172S4

theorem block172RightChunk000ParamsCertificate_eq_true :
    block172RightChunk000ParamsCertificate = true := by
  native_decide

theorem block172_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block172RightChunk000L : ℝ) (block172RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block172S1 : ℝ))
    (hy2ne : y ≠ (block172S2 : ℝ))
    (hy3ne : y ≠ (block172S3 : ℝ))
    (hy4ne : y ≠ (block172S4 : ℝ)) :
    0 < block172V y := by
  have hcert := block172RightChunk000Certificate_eq_true
  unfold block172RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block172RightChunk000) (lo := block172RightChunk000L) (hi := block172RightChunk000R)
    (w1 := block172W1) (w2 := block172W2) (w3 := block172W3) (w4 := block172W4)
    (s1 := block172S1) (s2 := block172S2) (s3 := block172S3) (s4 := block172S4)
    hboxes hcover block172RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block172RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block172RightChunk001 block172W1 block172W2 block172W3 block172W4 block172S1 block172S2 block172S3 block172S4

theorem block172RightChunk001ParamsCertificate_eq_true :
    block172RightChunk001ParamsCertificate = true := by
  native_decide

theorem block172_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block172RightChunk001L : ℝ) (block172RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block172S1 : ℝ))
    (hy2ne : y ≠ (block172S2 : ℝ))
    (hy3ne : y ≠ (block172S3 : ℝ))
    (hy4ne : y ≠ (block172S4 : ℝ)) :
    0 < block172V y := by
  have hcert := block172RightChunk001Certificate_eq_true
  unfold block172RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block172RightChunk001) (lo := block172RightChunk001L) (hi := block172RightChunk001R)
    (w1 := block172W1) (w2 := block172W2) (w3 := block172W3) (w4 := block172W4)
    (s1 := block172S1) (s2 := block172S2) (s3 := block172S3) (s4 := block172S4)
    hboxes hcover block172RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block172_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block172RightL : ℝ) (block172RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block172S1 : ℝ))
    (hy2ne : y ≠ (block172S2 : ℝ))
    (hy3ne : y ≠ (block172S3 : ℝ))
    (hy4ne : y ≠ (block172S4 : ℝ)) :
    0 < block172V y := by
  by_cases h0 : y ≤ (block172RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block172RightChunk000L : ℝ) (block172RightChunk000R : ℝ) := by
      have hL : (block172RightChunk000L : ℝ) = (block172RightL : ℝ) := by
        norm_num [block172RightChunk000L, block172RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block172_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block172RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block172RightChunk001L : ℝ) = (block172RightChunk000R : ℝ) := by
      norm_num [block172RightChunk001L, block172RightChunk000R]
    have hR : (block172RightChunk001R : ℝ) = (block172RightR : ℝ) := by
      norm_num [block172RightChunk001R, block172RightR]
    have hyc : y ∈ Icc (block172RightChunk001L : ℝ) (block172RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block172_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block172_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block172LeftL : ℝ) (block172LeftR : ℝ) →
    y ≠ 0 → y ≠ (block172S1 : ℝ) → y ≠ (block172S2 : ℝ) →
    y ≠ (block172S3 : ℝ) → y ≠ (block172S4 : ℝ) → 0 < block172V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block172RightL : ℝ) (block172RightR : ℝ) →
    y ≠ 0 → y ≠ (block172S1 : ℝ) → y ≠ (block172S2 : ℝ) →
    y ≠ (block172S3 : ℝ) → y ≠ (block172S4 : ℝ) → 0 < block172V y)

theorem block172_reallog_certificate_proof :
    block172_reallog_certificate := by
  exact ⟨block172_left_V_pos, block172_right_V_pos⟩

end Block172
end M1817475
end Erdos1038Lean
