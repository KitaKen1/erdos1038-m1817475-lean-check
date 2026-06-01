import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block536

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block536

open Set

def block536W1 : Rat := ((2510447341686629 : Rat) / 6250000000000000)
def block536W2 : Rat := (0 : Rat)
def block536W3 : Rat := ((45447143043353977 : Rat) / 100000000000000000)
def block536W4 : Rat := (0 : Rat)
def block536S1 : Rat := ((18174751 : Rat) / 10000000)
def block536S2 : Rat := ((511587 : Rat) / 200000)
def block536S3 : Rat := ((129655235803571428751 : Rat) / 50000000000000000000)
def block536S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block536V (y : ℝ) : ℝ :=
  ratPotential block536W1 block536W2 block536W3 block536W4 block536S1 block536S2 block536S3 block536S4 y

def block536LeftParamsCertificate : Bool :=
  allBoxesSameParams block536LeftBoxes block536W1 block536W2 block536W3 block536W4 block536S1 block536S2 block536S3 block536S4

theorem block536LeftParamsCertificate_eq_true :
    block536LeftParamsCertificate = true := by
  native_decide

theorem block536_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block536LeftL : ℝ) (block536LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block536S1 : ℝ))
    (hy2ne : y ≠ (block536S2 : ℝ))
    (hy3ne : y ≠ (block536S3 : ℝ))
    (hy4ne : y ≠ (block536S4 : ℝ)) :
    0 < block536V y := by
  have hcert := block536LeftCertificate_eq_true
  unfold block536LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block536LeftBoxes) (lo := block536LeftL) (hi := block536LeftR)
    (w1 := block536W1) (w2 := block536W2) (w3 := block536W3) (w4 := block536W4)
    (s1 := block536S1) (s2 := block536S2) (s3 := block536S3) (s4 := block536S4)
    hboxes hcover block536LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block536RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block536RightChunk000 block536W1 block536W2 block536W3 block536W4 block536S1 block536S2 block536S3 block536S4

theorem block536RightChunk000ParamsCertificate_eq_true :
    block536RightChunk000ParamsCertificate = true := by
  native_decide

theorem block536_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block536RightChunk000L : ℝ) (block536RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block536S1 : ℝ))
    (hy2ne : y ≠ (block536S2 : ℝ))
    (hy3ne : y ≠ (block536S3 : ℝ))
    (hy4ne : y ≠ (block536S4 : ℝ)) :
    0 < block536V y := by
  have hcert := block536RightChunk000Certificate_eq_true
  unfold block536RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block536RightChunk000) (lo := block536RightChunk000L) (hi := block536RightChunk000R)
    (w1 := block536W1) (w2 := block536W2) (w3 := block536W3) (w4 := block536W4)
    (s1 := block536S1) (s2 := block536S2) (s3 := block536S3) (s4 := block536S4)
    hboxes hcover block536RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block536_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block536RightL : ℝ) (block536RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block536S1 : ℝ))
    (hy2ne : y ≠ (block536S2 : ℝ))
    (hy3ne : y ≠ (block536S3 : ℝ))
    (hy4ne : y ≠ (block536S4 : ℝ)) :
    0 < block536V y := by
  have hL : (block536RightChunk000L : ℝ) = (block536RightL : ℝ) := by
    norm_num [block536RightChunk000L, block536RightL]
  have hR : (block536RightChunk000R : ℝ) = (block536RightR : ℝ) := by
    norm_num [block536RightChunk000R, block536RightR]
  have hyc : y ∈ Icc (block536RightChunk000L : ℝ) (block536RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block536_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block536_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block536LeftL : ℝ) (block536LeftR : ℝ) →
    y ≠ 0 → y ≠ (block536S1 : ℝ) → y ≠ (block536S2 : ℝ) →
    y ≠ (block536S3 : ℝ) → y ≠ (block536S4 : ℝ) → 0 < block536V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block536RightL : ℝ) (block536RightR : ℝ) →
    y ≠ 0 → y ≠ (block536S1 : ℝ) → y ≠ (block536S2 : ℝ) →
    y ≠ (block536S3 : ℝ) → y ≠ (block536S4 : ℝ) → 0 < block536V y)

theorem block536_reallog_certificate_proof :
    block536_reallog_certificate := by
  exact ⟨block536_left_V_pos, block536_right_V_pos⟩

end Block536
end M1817475
end Erdos1038Lean
