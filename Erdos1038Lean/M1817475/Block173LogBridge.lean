import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block173

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block173

open Set

def block173W1 : Rat := ((9061190969386619 : Rat) / 5000000000000000)
def block173W2 : Rat := (0 : Rat)
def block173W3 : Rat := ((8474575213639879 : Rat) / 50000000000000000)
def block173W4 : Rat := ((156114527914929 : Rat) / 1562500000000000)
def block173S1 : Rat := ((18174751 : Rat) / 10000000)
def block173S2 : Rat := ((511587 : Rat) / 200000)
def block173S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block173S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block173V (y : ℝ) : ℝ :=
  ratPotential block173W1 block173W2 block173W3 block173W4 block173S1 block173S2 block173S3 block173S4 y

def block173LeftParamsCertificate : Bool :=
  allBoxesSameParams block173LeftBoxes block173W1 block173W2 block173W3 block173W4 block173S1 block173S2 block173S3 block173S4

theorem block173LeftParamsCertificate_eq_true :
    block173LeftParamsCertificate = true := by
  native_decide

theorem block173_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block173LeftL : ℝ) (block173LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block173S1 : ℝ))
    (hy2ne : y ≠ (block173S2 : ℝ))
    (hy3ne : y ≠ (block173S3 : ℝ))
    (hy4ne : y ≠ (block173S4 : ℝ)) :
    0 < block173V y := by
  have hcert := block173LeftCertificate_eq_true
  unfold block173LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block173LeftBoxes) (lo := block173LeftL) (hi := block173LeftR)
    (w1 := block173W1) (w2 := block173W2) (w3 := block173W3) (w4 := block173W4)
    (s1 := block173S1) (s2 := block173S2) (s3 := block173S3) (s4 := block173S4)
    hboxes hcover block173LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block173RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block173RightChunk000 block173W1 block173W2 block173W3 block173W4 block173S1 block173S2 block173S3 block173S4

theorem block173RightChunk000ParamsCertificate_eq_true :
    block173RightChunk000ParamsCertificate = true := by
  native_decide

theorem block173_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block173RightChunk000L : ℝ) (block173RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block173S1 : ℝ))
    (hy2ne : y ≠ (block173S2 : ℝ))
    (hy3ne : y ≠ (block173S3 : ℝ))
    (hy4ne : y ≠ (block173S4 : ℝ)) :
    0 < block173V y := by
  have hcert := block173RightChunk000Certificate_eq_true
  unfold block173RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block173RightChunk000) (lo := block173RightChunk000L) (hi := block173RightChunk000R)
    (w1 := block173W1) (w2 := block173W2) (w3 := block173W3) (w4 := block173W4)
    (s1 := block173S1) (s2 := block173S2) (s3 := block173S3) (s4 := block173S4)
    hboxes hcover block173RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block173RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block173RightChunk001 block173W1 block173W2 block173W3 block173W4 block173S1 block173S2 block173S3 block173S4

theorem block173RightChunk001ParamsCertificate_eq_true :
    block173RightChunk001ParamsCertificate = true := by
  native_decide

theorem block173_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block173RightChunk001L : ℝ) (block173RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block173S1 : ℝ))
    (hy2ne : y ≠ (block173S2 : ℝ))
    (hy3ne : y ≠ (block173S3 : ℝ))
    (hy4ne : y ≠ (block173S4 : ℝ)) :
    0 < block173V y := by
  have hcert := block173RightChunk001Certificate_eq_true
  unfold block173RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block173RightChunk001) (lo := block173RightChunk001L) (hi := block173RightChunk001R)
    (w1 := block173W1) (w2 := block173W2) (w3 := block173W3) (w4 := block173W4)
    (s1 := block173S1) (s2 := block173S2) (s3 := block173S3) (s4 := block173S4)
    hboxes hcover block173RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block173_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block173RightL : ℝ) (block173RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block173S1 : ℝ))
    (hy2ne : y ≠ (block173S2 : ℝ))
    (hy3ne : y ≠ (block173S3 : ℝ))
    (hy4ne : y ≠ (block173S4 : ℝ)) :
    0 < block173V y := by
  by_cases h0 : y ≤ (block173RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block173RightChunk000L : ℝ) (block173RightChunk000R : ℝ) := by
      have hL : (block173RightChunk000L : ℝ) = (block173RightL : ℝ) := by
        norm_num [block173RightChunk000L, block173RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block173_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block173RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block173RightChunk001L : ℝ) = (block173RightChunk000R : ℝ) := by
      norm_num [block173RightChunk001L, block173RightChunk000R]
    have hR : (block173RightChunk001R : ℝ) = (block173RightR : ℝ) := by
      norm_num [block173RightChunk001R, block173RightR]
    have hyc : y ∈ Icc (block173RightChunk001L : ℝ) (block173RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block173_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block173_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block173LeftL : ℝ) (block173LeftR : ℝ) →
    y ≠ 0 → y ≠ (block173S1 : ℝ) → y ≠ (block173S2 : ℝ) →
    y ≠ (block173S3 : ℝ) → y ≠ (block173S4 : ℝ) → 0 < block173V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block173RightL : ℝ) (block173RightR : ℝ) →
    y ≠ 0 → y ≠ (block173S1 : ℝ) → y ≠ (block173S2 : ℝ) →
    y ≠ (block173S3 : ℝ) → y ≠ (block173S4 : ℝ) → 0 < block173V y)

theorem block173_reallog_certificate_proof :
    block173_reallog_certificate := by
  exact ⟨block173_left_V_pos, block173_right_V_pos⟩

end Block173
end M1817475
end Erdos1038Lean
