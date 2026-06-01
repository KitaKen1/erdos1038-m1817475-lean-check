import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block345

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block345

open Set

def block345W1 : Rat := ((9169760186942413 : Rat) / 10000000000000000)
def block345W2 : Rat := ((237102316574397 : Rat) / 5000000000000000)
def block345W3 : Rat := ((14763367026285173 : Rat) / 100000000000000000)
def block345W4 : Rat := ((2756978001545421 : Rat) / 20000000000000000)
def block345S1 : Rat := ((18174751 : Rat) / 10000000)
def block345S2 : Rat := ((511587 : Rat) / 200000)
def block345S3 : Rat := ((133389115267857142873 : Rat) / 50000000000000000000)
def block345S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block345V (y : ℝ) : ℝ :=
  ratPotential block345W1 block345W2 block345W3 block345W4 block345S1 block345S2 block345S3 block345S4 y

def block345LeftParamsCertificate : Bool :=
  allBoxesSameParams block345LeftBoxes block345W1 block345W2 block345W3 block345W4 block345S1 block345S2 block345S3 block345S4

theorem block345LeftParamsCertificate_eq_true :
    block345LeftParamsCertificate = true := by
  native_decide

theorem block345_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block345LeftL : ℝ) (block345LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block345S1 : ℝ))
    (hy2ne : y ≠ (block345S2 : ℝ))
    (hy3ne : y ≠ (block345S3 : ℝ))
    (hy4ne : y ≠ (block345S4 : ℝ)) :
    0 < block345V y := by
  have hcert := block345LeftCertificate_eq_true
  unfold block345LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block345LeftBoxes) (lo := block345LeftL) (hi := block345LeftR)
    (w1 := block345W1) (w2 := block345W2) (w3 := block345W3) (w4 := block345W4)
    (s1 := block345S1) (s2 := block345S2) (s3 := block345S3) (s4 := block345S4)
    hboxes hcover block345LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block345RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block345RightChunk000 block345W1 block345W2 block345W3 block345W4 block345S1 block345S2 block345S3 block345S4

theorem block345RightChunk000ParamsCertificate_eq_true :
    block345RightChunk000ParamsCertificate = true := by
  native_decide

theorem block345_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block345RightChunk000L : ℝ) (block345RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block345S1 : ℝ))
    (hy2ne : y ≠ (block345S2 : ℝ))
    (hy3ne : y ≠ (block345S3 : ℝ))
    (hy4ne : y ≠ (block345S4 : ℝ)) :
    0 < block345V y := by
  have hcert := block345RightChunk000Certificate_eq_true
  unfold block345RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block345RightChunk000) (lo := block345RightChunk000L) (hi := block345RightChunk000R)
    (w1 := block345W1) (w2 := block345W2) (w3 := block345W3) (w4 := block345W4)
    (s1 := block345S1) (s2 := block345S2) (s3 := block345S3) (s4 := block345S4)
    hboxes hcover block345RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block345_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block345RightL : ℝ) (block345RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block345S1 : ℝ))
    (hy2ne : y ≠ (block345S2 : ℝ))
    (hy3ne : y ≠ (block345S3 : ℝ))
    (hy4ne : y ≠ (block345S4 : ℝ)) :
    0 < block345V y := by
  have hL : (block345RightChunk000L : ℝ) = (block345RightL : ℝ) := by
    norm_num [block345RightChunk000L, block345RightL]
  have hR : (block345RightChunk000R : ℝ) = (block345RightR : ℝ) := by
    norm_num [block345RightChunk000R, block345RightR]
  have hyc : y ∈ Icc (block345RightChunk000L : ℝ) (block345RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block345_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block345_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block345LeftL : ℝ) (block345LeftR : ℝ) →
    y ≠ 0 → y ≠ (block345S1 : ℝ) → y ≠ (block345S2 : ℝ) →
    y ≠ (block345S3 : ℝ) → y ≠ (block345S4 : ℝ) → 0 < block345V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block345RightL : ℝ) (block345RightR : ℝ) →
    y ≠ 0 → y ≠ (block345S1 : ℝ) → y ≠ (block345S2 : ℝ) →
    y ≠ (block345S3 : ℝ) → y ≠ (block345S4 : ℝ) → 0 < block345V y)

theorem block345_reallog_certificate_proof :
    block345_reallog_certificate := by
  exact ⟨block345_left_V_pos, block345_right_V_pos⟩

end Block345
end M1817475
end Erdos1038Lean
