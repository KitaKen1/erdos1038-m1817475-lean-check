import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block328

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block328

open Set

def block328W1 : Rat := ((9556106182834753 : Rat) / 10000000000000000)
def block328W2 : Rat := ((4752889916153827 : Rat) / 100000000000000000)
def block328W3 : Rat := ((1423557206171207 : Rat) / 10000000000000000)
def block328W4 : Rat := ((2729097987059903 : Rat) / 20000000000000000)
def block328S1 : Rat := ((18174751 : Rat) / 10000000)
def block328S2 : Rat := ((511587 : Rat) / 200000)
def block328S3 : Rat := ((107000619 : Rat) / 40000000)
def block328S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block328V (y : ℝ) : ℝ :=
  ratPotential block328W1 block328W2 block328W3 block328W4 block328S1 block328S2 block328S3 block328S4 y

def block328LeftParamsCertificate : Bool :=
  allBoxesSameParams block328LeftBoxes block328W1 block328W2 block328W3 block328W4 block328S1 block328S2 block328S3 block328S4

theorem block328LeftParamsCertificate_eq_true :
    block328LeftParamsCertificate = true := by
  native_decide

theorem block328_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block328LeftL : ℝ) (block328LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block328S1 : ℝ))
    (hy2ne : y ≠ (block328S2 : ℝ))
    (hy3ne : y ≠ (block328S3 : ℝ))
    (hy4ne : y ≠ (block328S4 : ℝ)) :
    0 < block328V y := by
  have hcert := block328LeftCertificate_eq_true
  unfold block328LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block328LeftBoxes) (lo := block328LeftL) (hi := block328LeftR)
    (w1 := block328W1) (w2 := block328W2) (w3 := block328W3) (w4 := block328W4)
    (s1 := block328S1) (s2 := block328S2) (s3 := block328S3) (s4 := block328S4)
    hboxes hcover block328LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block328RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block328RightChunk000 block328W1 block328W2 block328W3 block328W4 block328S1 block328S2 block328S3 block328S4

theorem block328RightChunk000ParamsCertificate_eq_true :
    block328RightChunk000ParamsCertificate = true := by
  native_decide

theorem block328_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block328RightChunk000L : ℝ) (block328RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block328S1 : ℝ))
    (hy2ne : y ≠ (block328S2 : ℝ))
    (hy3ne : y ≠ (block328S3 : ℝ))
    (hy4ne : y ≠ (block328S4 : ℝ)) :
    0 < block328V y := by
  have hcert := block328RightChunk000Certificate_eq_true
  unfold block328RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block328RightChunk000) (lo := block328RightChunk000L) (hi := block328RightChunk000R)
    (w1 := block328W1) (w2 := block328W2) (w3 := block328W3) (w4 := block328W4)
    (s1 := block328S1) (s2 := block328S2) (s3 := block328S3) (s4 := block328S4)
    hboxes hcover block328RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block328_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block328RightL : ℝ) (block328RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block328S1 : ℝ))
    (hy2ne : y ≠ (block328S2 : ℝ))
    (hy3ne : y ≠ (block328S3 : ℝ))
    (hy4ne : y ≠ (block328S4 : ℝ)) :
    0 < block328V y := by
  have hL : (block328RightChunk000L : ℝ) = (block328RightL : ℝ) := by
    norm_num [block328RightChunk000L, block328RightL]
  have hR : (block328RightChunk000R : ℝ) = (block328RightR : ℝ) := by
    norm_num [block328RightChunk000R, block328RightR]
  have hyc : y ∈ Icc (block328RightChunk000L : ℝ) (block328RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block328_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block328_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block328LeftL : ℝ) (block328LeftR : ℝ) →
    y ≠ 0 → y ≠ (block328S1 : ℝ) → y ≠ (block328S2 : ℝ) →
    y ≠ (block328S3 : ℝ) → y ≠ (block328S4 : ℝ) → 0 < block328V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block328RightL : ℝ) (block328RightR : ℝ) →
    y ≠ 0 → y ≠ (block328S1 : ℝ) → y ≠ (block328S2 : ℝ) →
    y ≠ (block328S3 : ℝ) → y ≠ (block328S4 : ℝ) → 0 < block328V y)

theorem block328_reallog_certificate_proof :
    block328_reallog_certificate := by
  exact ⟨block328_left_V_pos, block328_right_V_pos⟩

end Block328
end M1817475
end Erdos1038Lean
