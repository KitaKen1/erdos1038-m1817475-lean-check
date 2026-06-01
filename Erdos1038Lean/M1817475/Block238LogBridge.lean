import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block238

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block238

open Set

def block238W1 : Rat := ((4313190516053363 : Rat) / 5000000000000000)
def block238W2 : Rat := ((4225331090471827 : Rat) / 50000000000000000)
def block238W3 : Rat := ((4528663110283919 : Rat) / 25000000000000000)
def block238W4 : Rat := ((3554542138276179 : Rat) / 50000000000000000)
def block238S1 : Rat := ((18174751 : Rat) / 10000000)
def block238S2 : Rat := ((511587 : Rat) / 200000)
def block238S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block238S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block238V (y : ℝ) : ℝ :=
  ratPotential block238W1 block238W2 block238W3 block238W4 block238S1 block238S2 block238S3 block238S4 y

def block238LeftParamsCertificate : Bool :=
  allBoxesSameParams block238LeftBoxes block238W1 block238W2 block238W3 block238W4 block238S1 block238S2 block238S3 block238S4

theorem block238LeftParamsCertificate_eq_true :
    block238LeftParamsCertificate = true := by
  native_decide

theorem block238_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block238LeftL : ℝ) (block238LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block238S1 : ℝ))
    (hy2ne : y ≠ (block238S2 : ℝ))
    (hy3ne : y ≠ (block238S3 : ℝ))
    (hy4ne : y ≠ (block238S4 : ℝ)) :
    0 < block238V y := by
  have hcert := block238LeftCertificate_eq_true
  unfold block238LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block238LeftBoxes) (lo := block238LeftL) (hi := block238LeftR)
    (w1 := block238W1) (w2 := block238W2) (w3 := block238W3) (w4 := block238W4)
    (s1 := block238S1) (s2 := block238S2) (s3 := block238S3) (s4 := block238S4)
    hboxes hcover block238LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block238RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block238RightChunk000 block238W1 block238W2 block238W3 block238W4 block238S1 block238S2 block238S3 block238S4

theorem block238RightChunk000ParamsCertificate_eq_true :
    block238RightChunk000ParamsCertificate = true := by
  native_decide

theorem block238_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block238RightChunk000L : ℝ) (block238RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block238S1 : ℝ))
    (hy2ne : y ≠ (block238S2 : ℝ))
    (hy3ne : y ≠ (block238S3 : ℝ))
    (hy4ne : y ≠ (block238S4 : ℝ)) :
    0 < block238V y := by
  have hcert := block238RightChunk000Certificate_eq_true
  unfold block238RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block238RightChunk000) (lo := block238RightChunk000L) (hi := block238RightChunk000R)
    (w1 := block238W1) (w2 := block238W2) (w3 := block238W3) (w4 := block238W4)
    (s1 := block238S1) (s2 := block238S2) (s3 := block238S3) (s4 := block238S4)
    hboxes hcover block238RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block238RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block238RightChunk001 block238W1 block238W2 block238W3 block238W4 block238S1 block238S2 block238S3 block238S4

theorem block238RightChunk001ParamsCertificate_eq_true :
    block238RightChunk001ParamsCertificate = true := by
  native_decide

theorem block238_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block238RightChunk001L : ℝ) (block238RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block238S1 : ℝ))
    (hy2ne : y ≠ (block238S2 : ℝ))
    (hy3ne : y ≠ (block238S3 : ℝ))
    (hy4ne : y ≠ (block238S4 : ℝ)) :
    0 < block238V y := by
  have hcert := block238RightChunk001Certificate_eq_true
  unfold block238RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block238RightChunk001) (lo := block238RightChunk001L) (hi := block238RightChunk001R)
    (w1 := block238W1) (w2 := block238W2) (w3 := block238W3) (w4 := block238W4)
    (s1 := block238S1) (s2 := block238S2) (s3 := block238S3) (s4 := block238S4)
    hboxes hcover block238RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block238_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block238RightL : ℝ) (block238RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block238S1 : ℝ))
    (hy2ne : y ≠ (block238S2 : ℝ))
    (hy3ne : y ≠ (block238S3 : ℝ))
    (hy4ne : y ≠ (block238S4 : ℝ)) :
    0 < block238V y := by
  by_cases h0 : y ≤ (block238RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block238RightChunk000L : ℝ) (block238RightChunk000R : ℝ) := by
      have hL : (block238RightChunk000L : ℝ) = (block238RightL : ℝ) := by
        norm_num [block238RightChunk000L, block238RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block238_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block238RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block238RightChunk001L : ℝ) = (block238RightChunk000R : ℝ) := by
      norm_num [block238RightChunk001L, block238RightChunk000R]
    have hR : (block238RightChunk001R : ℝ) = (block238RightR : ℝ) := by
      norm_num [block238RightChunk001R, block238RightR]
    have hyc : y ∈ Icc (block238RightChunk001L : ℝ) (block238RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block238_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block238_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block238LeftL : ℝ) (block238LeftR : ℝ) →
    y ≠ 0 → y ≠ (block238S1 : ℝ) → y ≠ (block238S2 : ℝ) →
    y ≠ (block238S3 : ℝ) → y ≠ (block238S4 : ℝ) → 0 < block238V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block238RightL : ℝ) (block238RightR : ℝ) →
    y ≠ 0 → y ≠ (block238S1 : ℝ) → y ≠ (block238S2 : ℝ) →
    y ≠ (block238S3 : ℝ) → y ≠ (block238S4 : ℝ) → 0 < block238V y)

theorem block238_reallog_certificate_proof :
    block238_reallog_certificate := by
  exact ⟨block238_left_V_pos, block238_right_V_pos⟩

end Block238
end M1817475
end Erdos1038Lean
