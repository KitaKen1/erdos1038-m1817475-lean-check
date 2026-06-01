import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block503

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block503

open Set

def block503W1 : Rat := ((1814911701041529 : Rat) / 4000000000000000)
def block503W2 : Rat := (0 : Rat)
def block503W3 : Rat := ((4214038934602169 : Rat) / 10000000000000000)
def block503W4 : Rat := ((158181470880089 : Rat) / 10000000000000000)
def block503S1 : Rat := ((18174751 : Rat) / 10000000)
def block503S2 : Rat := ((511587 : Rat) / 200000)
def block503S3 : Rat := ((130300356339285714437 : Rat) / 50000000000000000000)
def block503S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block503V (y : ℝ) : ℝ :=
  ratPotential block503W1 block503W2 block503W3 block503W4 block503S1 block503S2 block503S3 block503S4 y

def block503LeftParamsCertificate : Bool :=
  allBoxesSameParams block503LeftBoxes block503W1 block503W2 block503W3 block503W4 block503S1 block503S2 block503S3 block503S4

theorem block503LeftParamsCertificate_eq_true :
    block503LeftParamsCertificate = true := by
  native_decide

theorem block503_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block503LeftL : ℝ) (block503LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block503S1 : ℝ))
    (hy2ne : y ≠ (block503S2 : ℝ))
    (hy3ne : y ≠ (block503S3 : ℝ))
    (hy4ne : y ≠ (block503S4 : ℝ)) :
    0 < block503V y := by
  have hcert := block503LeftCertificate_eq_true
  unfold block503LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block503LeftBoxes) (lo := block503LeftL) (hi := block503LeftR)
    (w1 := block503W1) (w2 := block503W2) (w3 := block503W3) (w4 := block503W4)
    (s1 := block503S1) (s2 := block503S2) (s3 := block503S3) (s4 := block503S4)
    hboxes hcover block503LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block503RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block503RightChunk000 block503W1 block503W2 block503W3 block503W4 block503S1 block503S2 block503S3 block503S4

theorem block503RightChunk000ParamsCertificate_eq_true :
    block503RightChunk000ParamsCertificate = true := by
  native_decide

theorem block503_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block503RightChunk000L : ℝ) (block503RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block503S1 : ℝ))
    (hy2ne : y ≠ (block503S2 : ℝ))
    (hy3ne : y ≠ (block503S3 : ℝ))
    (hy4ne : y ≠ (block503S4 : ℝ)) :
    0 < block503V y := by
  have hcert := block503RightChunk000Certificate_eq_true
  unfold block503RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block503RightChunk000) (lo := block503RightChunk000L) (hi := block503RightChunk000R)
    (w1 := block503W1) (w2 := block503W2) (w3 := block503W3) (w4 := block503W4)
    (s1 := block503S1) (s2 := block503S2) (s3 := block503S3) (s4 := block503S4)
    hboxes hcover block503RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block503_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block503RightL : ℝ) (block503RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block503S1 : ℝ))
    (hy2ne : y ≠ (block503S2 : ℝ))
    (hy3ne : y ≠ (block503S3 : ℝ))
    (hy4ne : y ≠ (block503S4 : ℝ)) :
    0 < block503V y := by
  have hL : (block503RightChunk000L : ℝ) = (block503RightL : ℝ) := by
    norm_num [block503RightChunk000L, block503RightL]
  have hR : (block503RightChunk000R : ℝ) = (block503RightR : ℝ) := by
    norm_num [block503RightChunk000R, block503RightR]
  have hyc : y ∈ Icc (block503RightChunk000L : ℝ) (block503RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block503_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block503_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block503LeftL : ℝ) (block503LeftR : ℝ) →
    y ≠ 0 → y ≠ (block503S1 : ℝ) → y ≠ (block503S2 : ℝ) →
    y ≠ (block503S3 : ℝ) → y ≠ (block503S4 : ℝ) → 0 < block503V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block503RightL : ℝ) (block503RightR : ℝ) →
    y ≠ 0 → y ≠ (block503S1 : ℝ) → y ≠ (block503S2 : ℝ) →
    y ≠ (block503S3 : ℝ) → y ≠ (block503S4 : ℝ) → 0 < block503V y)

theorem block503_reallog_certificate_proof :
    block503_reallog_certificate := by
  exact ⟨block503_left_V_pos, block503_right_V_pos⟩

end Block503
end M1817475
end Erdos1038Lean
