import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block187

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block187

open Set

def block187W1 : Rat := ((1761981969925977 : Rat) / 1000000000000000)
def block187W2 : Rat := (0 : Rat)
def block187W3 : Rat := ((1778078509119177 : Rat) / 10000000000000000)
def block187W4 : Rat := ((9404285715912131 : Rat) / 100000000000000000)
def block187S1 : Rat := ((18174751 : Rat) / 10000000)
def block187S2 : Rat := ((511587 : Rat) / 200000)
def block187S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block187S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block187V (y : ℝ) : ℝ :=
  ratPotential block187W1 block187W2 block187W3 block187W4 block187S1 block187S2 block187S3 block187S4 y

def block187LeftParamsCertificate : Bool :=
  allBoxesSameParams block187LeftBoxes block187W1 block187W2 block187W3 block187W4 block187S1 block187S2 block187S3 block187S4

theorem block187LeftParamsCertificate_eq_true :
    block187LeftParamsCertificate = true := by
  native_decide

theorem block187_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block187LeftL : ℝ) (block187LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block187S1 : ℝ))
    (hy2ne : y ≠ (block187S2 : ℝ))
    (hy3ne : y ≠ (block187S3 : ℝ))
    (hy4ne : y ≠ (block187S4 : ℝ)) :
    0 < block187V y := by
  have hcert := block187LeftCertificate_eq_true
  unfold block187LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block187LeftBoxes) (lo := block187LeftL) (hi := block187LeftR)
    (w1 := block187W1) (w2 := block187W2) (w3 := block187W3) (w4 := block187W4)
    (s1 := block187S1) (s2 := block187S2) (s3 := block187S3) (s4 := block187S4)
    hboxes hcover block187LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block187RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block187RightChunk000 block187W1 block187W2 block187W3 block187W4 block187S1 block187S2 block187S3 block187S4

theorem block187RightChunk000ParamsCertificate_eq_true :
    block187RightChunk000ParamsCertificate = true := by
  native_decide

theorem block187_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block187RightChunk000L : ℝ) (block187RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block187S1 : ℝ))
    (hy2ne : y ≠ (block187S2 : ℝ))
    (hy3ne : y ≠ (block187S3 : ℝ))
    (hy4ne : y ≠ (block187S4 : ℝ)) :
    0 < block187V y := by
  have hcert := block187RightChunk000Certificate_eq_true
  unfold block187RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block187RightChunk000) (lo := block187RightChunk000L) (hi := block187RightChunk000R)
    (w1 := block187W1) (w2 := block187W2) (w3 := block187W3) (w4 := block187W4)
    (s1 := block187S1) (s2 := block187S2) (s3 := block187S3) (s4 := block187S4)
    hboxes hcover block187RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block187RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block187RightChunk001 block187W1 block187W2 block187W3 block187W4 block187S1 block187S2 block187S3 block187S4

theorem block187RightChunk001ParamsCertificate_eq_true :
    block187RightChunk001ParamsCertificate = true := by
  native_decide

theorem block187_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block187RightChunk001L : ℝ) (block187RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block187S1 : ℝ))
    (hy2ne : y ≠ (block187S2 : ℝ))
    (hy3ne : y ≠ (block187S3 : ℝ))
    (hy4ne : y ≠ (block187S4 : ℝ)) :
    0 < block187V y := by
  have hcert := block187RightChunk001Certificate_eq_true
  unfold block187RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block187RightChunk001) (lo := block187RightChunk001L) (hi := block187RightChunk001R)
    (w1 := block187W1) (w2 := block187W2) (w3 := block187W3) (w4 := block187W4)
    (s1 := block187S1) (s2 := block187S2) (s3 := block187S3) (s4 := block187S4)
    hboxes hcover block187RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block187_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block187RightL : ℝ) (block187RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block187S1 : ℝ))
    (hy2ne : y ≠ (block187S2 : ℝ))
    (hy3ne : y ≠ (block187S3 : ℝ))
    (hy4ne : y ≠ (block187S4 : ℝ)) :
    0 < block187V y := by
  by_cases h0 : y ≤ (block187RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block187RightChunk000L : ℝ) (block187RightChunk000R : ℝ) := by
      have hL : (block187RightChunk000L : ℝ) = (block187RightL : ℝ) := by
        norm_num [block187RightChunk000L, block187RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block187_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block187RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block187RightChunk001L : ℝ) = (block187RightChunk000R : ℝ) := by
      norm_num [block187RightChunk001L, block187RightChunk000R]
    have hR : (block187RightChunk001R : ℝ) = (block187RightR : ℝ) := by
      norm_num [block187RightChunk001R, block187RightR]
    have hyc : y ∈ Icc (block187RightChunk001L : ℝ) (block187RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block187_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block187_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block187LeftL : ℝ) (block187LeftR : ℝ) →
    y ≠ 0 → y ≠ (block187S1 : ℝ) → y ≠ (block187S2 : ℝ) →
    y ≠ (block187S3 : ℝ) → y ≠ (block187S4 : ℝ) → 0 < block187V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block187RightL : ℝ) (block187RightR : ℝ) →
    y ≠ 0 → y ≠ (block187S1 : ℝ) → y ≠ (block187S2 : ℝ) →
    y ≠ (block187S3 : ℝ) → y ≠ (block187S4 : ℝ) → 0 < block187V y)

theorem block187_reallog_certificate_proof :
    block187_reallog_certificate := by
  exact ⟨block187_left_V_pos, block187_right_V_pos⟩

end Block187
end M1817475
end Erdos1038Lean
