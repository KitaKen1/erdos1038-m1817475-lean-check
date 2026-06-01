import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block072

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block072

open Set

def block072W1 : Rat := ((781043693347641 : Rat) / 250000000000000)
def block072W2 : Rat := (0 : Rat)
def block072W3 : Rat := (0 : Rat)
def block072W4 : Rat := ((249668475288863 : Rat) / 1000000000000000)
def block072S1 : Rat := ((18174751 : Rat) / 10000000)
def block072S2 : Rat := ((511587 : Rat) / 200000)
def block072S3 : Rat := ((107000619 : Rat) / 40000000)
def block072S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block072V (y : ℝ) : ℝ :=
  ratPotential block072W1 block072W2 block072W3 block072W4 block072S1 block072S2 block072S3 block072S4 y

def block072LeftParamsCertificate : Bool :=
  allBoxesSameParams block072LeftBoxes block072W1 block072W2 block072W3 block072W4 block072S1 block072S2 block072S3 block072S4

theorem block072LeftParamsCertificate_eq_true :
    block072LeftParamsCertificate = true := by
  native_decide

theorem block072_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block072LeftL : ℝ) (block072LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block072S1 : ℝ))
    (hy2ne : y ≠ (block072S2 : ℝ))
    (hy3ne : y ≠ (block072S3 : ℝ))
    (hy4ne : y ≠ (block072S4 : ℝ)) :
    0 < block072V y := by
  have hcert := block072LeftCertificate_eq_true
  unfold block072LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block072LeftBoxes) (lo := block072LeftL) (hi := block072LeftR)
    (w1 := block072W1) (w2 := block072W2) (w3 := block072W3) (w4 := block072W4)
    (s1 := block072S1) (s2 := block072S2) (s3 := block072S3) (s4 := block072S4)
    hboxes hcover block072LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block072RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block072RightChunk000 block072W1 block072W2 block072W3 block072W4 block072S1 block072S2 block072S3 block072S4

theorem block072RightChunk000ParamsCertificate_eq_true :
    block072RightChunk000ParamsCertificate = true := by
  native_decide

theorem block072_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block072RightChunk000L : ℝ) (block072RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block072S1 : ℝ))
    (hy2ne : y ≠ (block072S2 : ℝ))
    (hy3ne : y ≠ (block072S3 : ℝ))
    (hy4ne : y ≠ (block072S4 : ℝ)) :
    0 < block072V y := by
  have hcert := block072RightChunk000Certificate_eq_true
  unfold block072RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block072RightChunk000) (lo := block072RightChunk000L) (hi := block072RightChunk000R)
    (w1 := block072W1) (w2 := block072W2) (w3 := block072W3) (w4 := block072W4)
    (s1 := block072S1) (s2 := block072S2) (s3 := block072S3) (s4 := block072S4)
    hboxes hcover block072RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block072_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block072RightL : ℝ) (block072RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block072S1 : ℝ))
    (hy2ne : y ≠ (block072S2 : ℝ))
    (hy3ne : y ≠ (block072S3 : ℝ))
    (hy4ne : y ≠ (block072S4 : ℝ)) :
    0 < block072V y := by
  have hL : (block072RightChunk000L : ℝ) = (block072RightL : ℝ) := by
    norm_num [block072RightChunk000L, block072RightL]
  have hR : (block072RightChunk000R : ℝ) = (block072RightR : ℝ) := by
    norm_num [block072RightChunk000R, block072RightR]
  have hyc : y ∈ Icc (block072RightChunk000L : ℝ) (block072RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block072_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block072_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block072LeftL : ℝ) (block072LeftR : ℝ) →
    y ≠ 0 → y ≠ (block072S1 : ℝ) → y ≠ (block072S2 : ℝ) →
    y ≠ (block072S3 : ℝ) → y ≠ (block072S4 : ℝ) → 0 < block072V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block072RightL : ℝ) (block072RightR : ℝ) →
    y ≠ 0 → y ≠ (block072S1 : ℝ) → y ≠ (block072S2 : ℝ) →
    y ≠ (block072S3 : ℝ) → y ≠ (block072S4 : ℝ) → 0 < block072V y)

theorem block072_reallog_certificate_proof :
    block072_reallog_certificate := by
  exact ⟨block072_left_V_pos, block072_right_V_pos⟩

end Block072
end M1817475
end Erdos1038Lean
