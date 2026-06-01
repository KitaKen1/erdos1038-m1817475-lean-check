import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block415

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block415

open Set

def block415W1 : Rat := ((3511913507677921 : Rat) / 5000000000000000)
def block415W2 : Rat := (0 : Rat)
def block415W3 : Rat := ((29144540902043103 : Rat) / 100000000000000000)
def block415W4 : Rat := ((8734654674988383 : Rat) / 100000000000000000)
def block415S1 : Rat := ((18174751 : Rat) / 10000000)
def block415S2 : Rat := ((511587 : Rat) / 200000)
def block415S3 : Rat := ((132020677767857142933 : Rat) / 50000000000000000000)
def block415S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block415V (y : ℝ) : ℝ :=
  ratPotential block415W1 block415W2 block415W3 block415W4 block415S1 block415S2 block415S3 block415S4 y

def block415LeftParamsCertificate : Bool :=
  allBoxesSameParams block415LeftBoxes block415W1 block415W2 block415W3 block415W4 block415S1 block415S2 block415S3 block415S4

theorem block415LeftParamsCertificate_eq_true :
    block415LeftParamsCertificate = true := by
  native_decide

theorem block415_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block415LeftL : ℝ) (block415LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block415S1 : ℝ))
    (hy2ne : y ≠ (block415S2 : ℝ))
    (hy3ne : y ≠ (block415S3 : ℝ))
    (hy4ne : y ≠ (block415S4 : ℝ)) :
    0 < block415V y := by
  have hcert := block415LeftCertificate_eq_true
  unfold block415LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block415LeftBoxes) (lo := block415LeftL) (hi := block415LeftR)
    (w1 := block415W1) (w2 := block415W2) (w3 := block415W3) (w4 := block415W4)
    (s1 := block415S1) (s2 := block415S2) (s3 := block415S3) (s4 := block415S4)
    hboxes hcover block415LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block415RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block415RightChunk000 block415W1 block415W2 block415W3 block415W4 block415S1 block415S2 block415S3 block415S4

theorem block415RightChunk000ParamsCertificate_eq_true :
    block415RightChunk000ParamsCertificate = true := by
  native_decide

theorem block415_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block415RightChunk000L : ℝ) (block415RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block415S1 : ℝ))
    (hy2ne : y ≠ (block415S2 : ℝ))
    (hy3ne : y ≠ (block415S3 : ℝ))
    (hy4ne : y ≠ (block415S4 : ℝ)) :
    0 < block415V y := by
  have hcert := block415RightChunk000Certificate_eq_true
  unfold block415RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block415RightChunk000) (lo := block415RightChunk000L) (hi := block415RightChunk000R)
    (w1 := block415W1) (w2 := block415W2) (w3 := block415W3) (w4 := block415W4)
    (s1 := block415S1) (s2 := block415S2) (s3 := block415S3) (s4 := block415S4)
    hboxes hcover block415RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block415RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block415RightChunk001 block415W1 block415W2 block415W3 block415W4 block415S1 block415S2 block415S3 block415S4

theorem block415RightChunk001ParamsCertificate_eq_true :
    block415RightChunk001ParamsCertificate = true := by
  native_decide

theorem block415_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block415RightChunk001L : ℝ) (block415RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block415S1 : ℝ))
    (hy2ne : y ≠ (block415S2 : ℝ))
    (hy3ne : y ≠ (block415S3 : ℝ))
    (hy4ne : y ≠ (block415S4 : ℝ)) :
    0 < block415V y := by
  have hcert := block415RightChunk001Certificate_eq_true
  unfold block415RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block415RightChunk001) (lo := block415RightChunk001L) (hi := block415RightChunk001R)
    (w1 := block415W1) (w2 := block415W2) (w3 := block415W3) (w4 := block415W4)
    (s1 := block415S1) (s2 := block415S2) (s3 := block415S3) (s4 := block415S4)
    hboxes hcover block415RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block415_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block415RightL : ℝ) (block415RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block415S1 : ℝ))
    (hy2ne : y ≠ (block415S2 : ℝ))
    (hy3ne : y ≠ (block415S3 : ℝ))
    (hy4ne : y ≠ (block415S4 : ℝ)) :
    0 < block415V y := by
  by_cases h0 : y ≤ (block415RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block415RightChunk000L : ℝ) (block415RightChunk000R : ℝ) := by
      have hL : (block415RightChunk000L : ℝ) = (block415RightL : ℝ) := by
        norm_num [block415RightChunk000L, block415RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block415_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block415RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block415RightChunk001L : ℝ) = (block415RightChunk000R : ℝ) := by
      norm_num [block415RightChunk001L, block415RightChunk000R]
    have hR : (block415RightChunk001R : ℝ) = (block415RightR : ℝ) := by
      norm_num [block415RightChunk001R, block415RightR]
    have hyc : y ∈ Icc (block415RightChunk001L : ℝ) (block415RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block415_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block415_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block415LeftL : ℝ) (block415LeftR : ℝ) →
    y ≠ 0 → y ≠ (block415S1 : ℝ) → y ≠ (block415S2 : ℝ) →
    y ≠ (block415S3 : ℝ) → y ≠ (block415S4 : ℝ) → 0 < block415V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block415RightL : ℝ) (block415RightR : ℝ) →
    y ≠ 0 → y ≠ (block415S1 : ℝ) → y ≠ (block415S2 : ℝ) →
    y ≠ (block415S3 : ℝ) → y ≠ (block415S4 : ℝ) → 0 < block415V y)

theorem block415_reallog_certificate_proof :
    block415_reallog_certificate := by
  exact ⟨block415_left_V_pos, block415_right_V_pos⟩

end Block415
end M1817475
end Erdos1038Lean
