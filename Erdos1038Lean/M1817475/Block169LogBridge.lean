import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block169

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block169

open Set

def block169W1 : Rat := ((4569007558247531 : Rat) / 2500000000000000)
def block169W2 : Rat := (0 : Rat)
def block169W3 : Rat := ((16699298570650783 : Rat) / 100000000000000000)
def block169W4 : Rat := ((10170006993501911 : Rat) / 100000000000000000)
def block169S1 : Rat := ((18174751 : Rat) / 10000000)
def block169S2 : Rat := ((511587 : Rat) / 200000)
def block169S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block169S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block169V (y : ℝ) : ℝ :=
  ratPotential block169W1 block169W2 block169W3 block169W4 block169S1 block169S2 block169S3 block169S4 y

def block169LeftParamsCertificate : Bool :=
  allBoxesSameParams block169LeftBoxes block169W1 block169W2 block169W3 block169W4 block169S1 block169S2 block169S3 block169S4

theorem block169LeftParamsCertificate_eq_true :
    block169LeftParamsCertificate = true := by
  native_decide

theorem block169_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block169LeftL : ℝ) (block169LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block169S1 : ℝ))
    (hy2ne : y ≠ (block169S2 : ℝ))
    (hy3ne : y ≠ (block169S3 : ℝ))
    (hy4ne : y ≠ (block169S4 : ℝ)) :
    0 < block169V y := by
  have hcert := block169LeftCertificate_eq_true
  unfold block169LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block169LeftBoxes) (lo := block169LeftL) (hi := block169LeftR)
    (w1 := block169W1) (w2 := block169W2) (w3 := block169W3) (w4 := block169W4)
    (s1 := block169S1) (s2 := block169S2) (s3 := block169S3) (s4 := block169S4)
    hboxes hcover block169LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block169RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block169RightChunk000 block169W1 block169W2 block169W3 block169W4 block169S1 block169S2 block169S3 block169S4

theorem block169RightChunk000ParamsCertificate_eq_true :
    block169RightChunk000ParamsCertificate = true := by
  native_decide

theorem block169_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block169RightChunk000L : ℝ) (block169RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block169S1 : ℝ))
    (hy2ne : y ≠ (block169S2 : ℝ))
    (hy3ne : y ≠ (block169S3 : ℝ))
    (hy4ne : y ≠ (block169S4 : ℝ)) :
    0 < block169V y := by
  have hcert := block169RightChunk000Certificate_eq_true
  unfold block169RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block169RightChunk000) (lo := block169RightChunk000L) (hi := block169RightChunk000R)
    (w1 := block169W1) (w2 := block169W2) (w3 := block169W3) (w4 := block169W4)
    (s1 := block169S1) (s2 := block169S2) (s3 := block169S3) (s4 := block169S4)
    hboxes hcover block169RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block169RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block169RightChunk001 block169W1 block169W2 block169W3 block169W4 block169S1 block169S2 block169S3 block169S4

theorem block169RightChunk001ParamsCertificate_eq_true :
    block169RightChunk001ParamsCertificate = true := by
  native_decide

theorem block169_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block169RightChunk001L : ℝ) (block169RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block169S1 : ℝ))
    (hy2ne : y ≠ (block169S2 : ℝ))
    (hy3ne : y ≠ (block169S3 : ℝ))
    (hy4ne : y ≠ (block169S4 : ℝ)) :
    0 < block169V y := by
  have hcert := block169RightChunk001Certificate_eq_true
  unfold block169RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block169RightChunk001) (lo := block169RightChunk001L) (hi := block169RightChunk001R)
    (w1 := block169W1) (w2 := block169W2) (w3 := block169W3) (w4 := block169W4)
    (s1 := block169S1) (s2 := block169S2) (s3 := block169S3) (s4 := block169S4)
    hboxes hcover block169RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block169_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block169RightL : ℝ) (block169RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block169S1 : ℝ))
    (hy2ne : y ≠ (block169S2 : ℝ))
    (hy3ne : y ≠ (block169S3 : ℝ))
    (hy4ne : y ≠ (block169S4 : ℝ)) :
    0 < block169V y := by
  by_cases h0 : y ≤ (block169RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block169RightChunk000L : ℝ) (block169RightChunk000R : ℝ) := by
      have hL : (block169RightChunk000L : ℝ) = (block169RightL : ℝ) := by
        norm_num [block169RightChunk000L, block169RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block169_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block169RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block169RightChunk001L : ℝ) = (block169RightChunk000R : ℝ) := by
      norm_num [block169RightChunk001L, block169RightChunk000R]
    have hR : (block169RightChunk001R : ℝ) = (block169RightR : ℝ) := by
      norm_num [block169RightChunk001R, block169RightR]
    have hyc : y ∈ Icc (block169RightChunk001L : ℝ) (block169RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block169_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block169_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block169LeftL : ℝ) (block169LeftR : ℝ) →
    y ≠ 0 → y ≠ (block169S1 : ℝ) → y ≠ (block169S2 : ℝ) →
    y ≠ (block169S3 : ℝ) → y ≠ (block169S4 : ℝ) → 0 < block169V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block169RightL : ℝ) (block169RightR : ℝ) →
    y ≠ 0 → y ≠ (block169S1 : ℝ) → y ≠ (block169S2 : ℝ) →
    y ≠ (block169S3 : ℝ) → y ≠ (block169S4 : ℝ) → 0 < block169V y)

theorem block169_reallog_certificate_proof :
    block169_reallog_certificate := by
  exact ⟨block169_left_V_pos, block169_right_V_pos⟩

end Block169
end M1817475
end Erdos1038Lean
