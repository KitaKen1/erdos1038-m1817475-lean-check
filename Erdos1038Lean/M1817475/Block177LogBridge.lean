import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block177

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block177

open Set

def block177W1 : Rat := ((18545744845872927 : Rat) / 10000000000000000)
def block177W2 : Rat := (0 : Rat)
def block177W3 : Rat := ((1753914171366439 : Rat) / 10000000000000000)
def block177W4 : Rat := ((915577353760947 : Rat) / 10000000000000000)
def block177S1 : Rat := ((18174751 : Rat) / 10000000)
def block177S2 : Rat := ((511587 : Rat) / 200000)
def block177S3 : Rat := ((68116755178571428517 : Rat) / 25000000000000000000)
def block177S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block177V (y : ℝ) : ℝ :=
  ratPotential block177W1 block177W2 block177W3 block177W4 block177S1 block177S2 block177S3 block177S4 y

def block177LeftParamsCertificate : Bool :=
  allBoxesSameParams block177LeftBoxes block177W1 block177W2 block177W3 block177W4 block177S1 block177S2 block177S3 block177S4

theorem block177LeftParamsCertificate_eq_true :
    block177LeftParamsCertificate = true := by
  native_decide

theorem block177_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block177LeftL : ℝ) (block177LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block177S1 : ℝ))
    (hy2ne : y ≠ (block177S2 : ℝ))
    (hy3ne : y ≠ (block177S3 : ℝ))
    (hy4ne : y ≠ (block177S4 : ℝ)) :
    0 < block177V y := by
  have hcert := block177LeftCertificate_eq_true
  unfold block177LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block177LeftBoxes) (lo := block177LeftL) (hi := block177LeftR)
    (w1 := block177W1) (w2 := block177W2) (w3 := block177W3) (w4 := block177W4)
    (s1 := block177S1) (s2 := block177S2) (s3 := block177S3) (s4 := block177S4)
    hboxes hcover block177LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block177RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block177RightChunk000 block177W1 block177W2 block177W3 block177W4 block177S1 block177S2 block177S3 block177S4

theorem block177RightChunk000ParamsCertificate_eq_true :
    block177RightChunk000ParamsCertificate = true := by
  native_decide

theorem block177_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block177RightChunk000L : ℝ) (block177RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block177S1 : ℝ))
    (hy2ne : y ≠ (block177S2 : ℝ))
    (hy3ne : y ≠ (block177S3 : ℝ))
    (hy4ne : y ≠ (block177S4 : ℝ)) :
    0 < block177V y := by
  have hcert := block177RightChunk000Certificate_eq_true
  unfold block177RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block177RightChunk000) (lo := block177RightChunk000L) (hi := block177RightChunk000R)
    (w1 := block177W1) (w2 := block177W2) (w3 := block177W3) (w4 := block177W4)
    (s1 := block177S1) (s2 := block177S2) (s3 := block177S3) (s4 := block177S4)
    hboxes hcover block177RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block177RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block177RightChunk001 block177W1 block177W2 block177W3 block177W4 block177S1 block177S2 block177S3 block177S4

theorem block177RightChunk001ParamsCertificate_eq_true :
    block177RightChunk001ParamsCertificate = true := by
  native_decide

theorem block177_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block177RightChunk001L : ℝ) (block177RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block177S1 : ℝ))
    (hy2ne : y ≠ (block177S2 : ℝ))
    (hy3ne : y ≠ (block177S3 : ℝ))
    (hy4ne : y ≠ (block177S4 : ℝ)) :
    0 < block177V y := by
  have hcert := block177RightChunk001Certificate_eq_true
  unfold block177RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block177RightChunk001) (lo := block177RightChunk001L) (hi := block177RightChunk001R)
    (w1 := block177W1) (w2 := block177W2) (w3 := block177W3) (w4 := block177W4)
    (s1 := block177S1) (s2 := block177S2) (s3 := block177S3) (s4 := block177S4)
    hboxes hcover block177RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block177_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block177RightL : ℝ) (block177RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block177S1 : ℝ))
    (hy2ne : y ≠ (block177S2 : ℝ))
    (hy3ne : y ≠ (block177S3 : ℝ))
    (hy4ne : y ≠ (block177S4 : ℝ)) :
    0 < block177V y := by
  by_cases h0 : y ≤ (block177RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block177RightChunk000L : ℝ) (block177RightChunk000R : ℝ) := by
      have hL : (block177RightChunk000L : ℝ) = (block177RightL : ℝ) := by
        norm_num [block177RightChunk000L, block177RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block177_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block177RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block177RightChunk001L : ℝ) = (block177RightChunk000R : ℝ) := by
      norm_num [block177RightChunk001L, block177RightChunk000R]
    have hR : (block177RightChunk001R : ℝ) = (block177RightR : ℝ) := by
      norm_num [block177RightChunk001R, block177RightR]
    have hyc : y ∈ Icc (block177RightChunk001L : ℝ) (block177RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block177_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block177_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block177LeftL : ℝ) (block177LeftR : ℝ) →
    y ≠ 0 → y ≠ (block177S1 : ℝ) → y ≠ (block177S2 : ℝ) →
    y ≠ (block177S3 : ℝ) → y ≠ (block177S4 : ℝ) → 0 < block177V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block177RightL : ℝ) (block177RightR : ℝ) →
    y ≠ 0 → y ≠ (block177S1 : ℝ) → y ≠ (block177S2 : ℝ) →
    y ≠ (block177S3 : ℝ) → y ≠ (block177S4 : ℝ) → 0 < block177V y)

theorem block177_reallog_certificate_proof :
    block177_reallog_certificate := by
  exact ⟨block177_left_V_pos, block177_right_V_pos⟩

end Block177
end M1817475
end Erdos1038Lean
