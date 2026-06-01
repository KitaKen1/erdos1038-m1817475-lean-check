import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block333

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block333

open Set

def block333W1 : Rat := ((9431664512849217 : Rat) / 10000000000000000)
def block333W2 : Rat := ((23607476404758753 : Rat) / 500000000000000000)
def block333W3 : Rat := ((2884709245648981 : Rat) / 20000000000000000)
def block333W4 : Rat := ((3425605842257877 : Rat) / 25000000000000000)
def block333S1 : Rat := ((18174751 : Rat) / 10000000)
def block333S2 : Rat := ((511587 : Rat) / 200000)
def block333S3 : Rat := ((133623704553571428577 : Rat) / 50000000000000000000)
def block333S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block333V (y : ℝ) : ℝ :=
  ratPotential block333W1 block333W2 block333W3 block333W4 block333S1 block333S2 block333S3 block333S4 y

def block333LeftParamsCertificate : Bool :=
  allBoxesSameParams block333LeftBoxes block333W1 block333W2 block333W3 block333W4 block333S1 block333S2 block333S3 block333S4

theorem block333LeftParamsCertificate_eq_true :
    block333LeftParamsCertificate = true := by
  native_decide

theorem block333_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block333LeftL : ℝ) (block333LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block333S1 : ℝ))
    (hy2ne : y ≠ (block333S2 : ℝ))
    (hy3ne : y ≠ (block333S3 : ℝ))
    (hy4ne : y ≠ (block333S4 : ℝ)) :
    0 < block333V y := by
  have hcert := block333LeftCertificate_eq_true
  unfold block333LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block333LeftBoxes) (lo := block333LeftL) (hi := block333LeftR)
    (w1 := block333W1) (w2 := block333W2) (w3 := block333W3) (w4 := block333W4)
    (s1 := block333S1) (s2 := block333S2) (s3 := block333S3) (s4 := block333S4)
    hboxes hcover block333LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block333RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block333RightChunk000 block333W1 block333W2 block333W3 block333W4 block333S1 block333S2 block333S3 block333S4

theorem block333RightChunk000ParamsCertificate_eq_true :
    block333RightChunk000ParamsCertificate = true := by
  native_decide

theorem block333_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block333RightChunk000L : ℝ) (block333RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block333S1 : ℝ))
    (hy2ne : y ≠ (block333S2 : ℝ))
    (hy3ne : y ≠ (block333S3 : ℝ))
    (hy4ne : y ≠ (block333S4 : ℝ)) :
    0 < block333V y := by
  have hcert := block333RightChunk000Certificate_eq_true
  unfold block333RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block333RightChunk000) (lo := block333RightChunk000L) (hi := block333RightChunk000R)
    (w1 := block333W1) (w2 := block333W2) (w3 := block333W3) (w4 := block333W4)
    (s1 := block333S1) (s2 := block333S2) (s3 := block333S3) (s4 := block333S4)
    hboxes hcover block333RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block333_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block333RightL : ℝ) (block333RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block333S1 : ℝ))
    (hy2ne : y ≠ (block333S2 : ℝ))
    (hy3ne : y ≠ (block333S3 : ℝ))
    (hy4ne : y ≠ (block333S4 : ℝ)) :
    0 < block333V y := by
  have hL : (block333RightChunk000L : ℝ) = (block333RightL : ℝ) := by
    norm_num [block333RightChunk000L, block333RightL]
  have hR : (block333RightChunk000R : ℝ) = (block333RightR : ℝ) := by
    norm_num [block333RightChunk000R, block333RightR]
  have hyc : y ∈ Icc (block333RightChunk000L : ℝ) (block333RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block333_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block333_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block333LeftL : ℝ) (block333LeftR : ℝ) →
    y ≠ 0 → y ≠ (block333S1 : ℝ) → y ≠ (block333S2 : ℝ) →
    y ≠ (block333S3 : ℝ) → y ≠ (block333S4 : ℝ) → 0 < block333V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block333RightL : ℝ) (block333RightR : ℝ) →
    y ≠ 0 → y ≠ (block333S1 : ℝ) → y ≠ (block333S2 : ℝ) →
    y ≠ (block333S3 : ℝ) → y ≠ (block333S4 : ℝ) → 0 < block333V y)

theorem block333_reallog_certificate_proof :
    block333_reallog_certificate := by
  exact ⟨block333_left_V_pos, block333_right_V_pos⟩

end Block333
end M1817475
end Erdos1038Lean
