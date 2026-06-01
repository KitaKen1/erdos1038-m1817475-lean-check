import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block005

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block005

open Set

def block005W1 : Rat := ((5894429855721839 : Rat) / 500000000000000)
def block005W2 : Rat := (0 : Rat)
def block005W3 : Rat := (0 : Rat)
def block005W4 : Rat := ((24956195071173903 : Rat) / 100000000000000000)
def block005S1 : Rat := ((18174751 : Rat) / 10000000)
def block005S2 : Rat := ((511587 : Rat) / 200000)
def block005S3 : Rat := ((107000619 : Rat) / 40000000)
def block005S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block005V (y : ℝ) : ℝ :=
  ratPotential block005W1 block005W2 block005W3 block005W4 block005S1 block005S2 block005S3 block005S4 y

def block005LeftParamsCertificate : Bool :=
  allBoxesSameParams block005LeftBoxes block005W1 block005W2 block005W3 block005W4 block005S1 block005S2 block005S3 block005S4

theorem block005LeftParamsCertificate_eq_true :
    block005LeftParamsCertificate = true := by
  native_decide

theorem block005_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block005LeftL : ℝ) (block005LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block005S1 : ℝ))
    (hy2ne : y ≠ (block005S2 : ℝ))
    (hy3ne : y ≠ (block005S3 : ℝ))
    (hy4ne : y ≠ (block005S4 : ℝ)) :
    0 < block005V y := by
  have hcert := block005LeftCertificate_eq_true
  unfold block005LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block005LeftBoxes) (lo := block005LeftL) (hi := block005LeftR)
    (w1 := block005W1) (w2 := block005W2) (w3 := block005W3) (w4 := block005W4)
    (s1 := block005S1) (s2 := block005S2) (s3 := block005S3) (s4 := block005S4)
    hboxes hcover block005LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block005RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block005RightChunk000 block005W1 block005W2 block005W3 block005W4 block005S1 block005S2 block005S3 block005S4

theorem block005RightChunk000ParamsCertificate_eq_true :
    block005RightChunk000ParamsCertificate = true := by
  native_decide

theorem block005_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block005RightChunk000L : ℝ) (block005RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block005S1 : ℝ))
    (hy2ne : y ≠ (block005S2 : ℝ))
    (hy3ne : y ≠ (block005S3 : ℝ))
    (hy4ne : y ≠ (block005S4 : ℝ)) :
    0 < block005V y := by
  have hcert := block005RightChunk000Certificate_eq_true
  unfold block005RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block005RightChunk000) (lo := block005RightChunk000L) (hi := block005RightChunk000R)
    (w1 := block005W1) (w2 := block005W2) (w3 := block005W3) (w4 := block005W4)
    (s1 := block005S1) (s2 := block005S2) (s3 := block005S3) (s4 := block005S4)
    hboxes hcover block005RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block005_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block005RightL : ℝ) (block005RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block005S1 : ℝ))
    (hy2ne : y ≠ (block005S2 : ℝ))
    (hy3ne : y ≠ (block005S3 : ℝ))
    (hy4ne : y ≠ (block005S4 : ℝ)) :
    0 < block005V y := by
  have hL : (block005RightChunk000L : ℝ) = (block005RightL : ℝ) := by
    norm_num [block005RightChunk000L, block005RightL]
  have hR : (block005RightChunk000R : ℝ) = (block005RightR : ℝ) := by
    norm_num [block005RightChunk000R, block005RightR]
  have hyc : y ∈ Icc (block005RightChunk000L : ℝ) (block005RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block005_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block005_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block005LeftL : ℝ) (block005LeftR : ℝ) →
    y ≠ 0 → y ≠ (block005S1 : ℝ) → y ≠ (block005S2 : ℝ) →
    y ≠ (block005S3 : ℝ) → y ≠ (block005S4 : ℝ) → 0 < block005V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block005RightL : ℝ) (block005RightR : ℝ) →
    y ≠ 0 → y ≠ (block005S1 : ℝ) → y ≠ (block005S2 : ℝ) →
    y ≠ (block005S3 : ℝ) → y ≠ (block005S4 : ℝ) → 0 < block005V y)

theorem block005_reallog_certificate_proof :
    block005_reallog_certificate := by
  exact ⟨block005_left_V_pos, block005_right_V_pos⟩

end Block005
end M1817475
end Erdos1038Lean
