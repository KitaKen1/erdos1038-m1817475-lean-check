import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block326

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block326

open Set

def block326W1 : Rat := ((9589201213159483 : Rat) / 10000000000000000)
def block326W2 : Rat := ((1172024281596559 : Rat) / 25000000000000000)
def block326W3 : Rat := ((14230971843071877 : Rat) / 100000000000000000)
def block326W4 : Rat := ((85448880239441 : Rat) / 625000000000000)
def block326S1 : Rat := ((18174751 : Rat) / 10000000)
def block326S2 : Rat := ((511587 : Rat) / 200000)
def block326S3 : Rat := ((107000619 : Rat) / 40000000)
def block326S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block326V (y : ℝ) : ℝ :=
  ratPotential block326W1 block326W2 block326W3 block326W4 block326S1 block326S2 block326S3 block326S4 y

def block326LeftParamsCertificate : Bool :=
  allBoxesSameParams block326LeftBoxes block326W1 block326W2 block326W3 block326W4 block326S1 block326S2 block326S3 block326S4

theorem block326LeftParamsCertificate_eq_true :
    block326LeftParamsCertificate = true := by
  native_decide

theorem block326_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block326LeftL : ℝ) (block326LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block326S1 : ℝ))
    (hy2ne : y ≠ (block326S2 : ℝ))
    (hy3ne : y ≠ (block326S3 : ℝ))
    (hy4ne : y ≠ (block326S4 : ℝ)) :
    0 < block326V y := by
  have hcert := block326LeftCertificate_eq_true
  unfold block326LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block326LeftBoxes) (lo := block326LeftL) (hi := block326LeftR)
    (w1 := block326W1) (w2 := block326W2) (w3 := block326W3) (w4 := block326W4)
    (s1 := block326S1) (s2 := block326S2) (s3 := block326S3) (s4 := block326S4)
    hboxes hcover block326LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block326RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block326RightChunk000 block326W1 block326W2 block326W3 block326W4 block326S1 block326S2 block326S3 block326S4

theorem block326RightChunk000ParamsCertificate_eq_true :
    block326RightChunk000ParamsCertificate = true := by
  native_decide

theorem block326_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block326RightChunk000L : ℝ) (block326RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block326S1 : ℝ))
    (hy2ne : y ≠ (block326S2 : ℝ))
    (hy3ne : y ≠ (block326S3 : ℝ))
    (hy4ne : y ≠ (block326S4 : ℝ)) :
    0 < block326V y := by
  have hcert := block326RightChunk000Certificate_eq_true
  unfold block326RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block326RightChunk000) (lo := block326RightChunk000L) (hi := block326RightChunk000R)
    (w1 := block326W1) (w2 := block326W2) (w3 := block326W3) (w4 := block326W4)
    (s1 := block326S1) (s2 := block326S2) (s3 := block326S3) (s4 := block326S4)
    hboxes hcover block326RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block326_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block326RightL : ℝ) (block326RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block326S1 : ℝ))
    (hy2ne : y ≠ (block326S2 : ℝ))
    (hy3ne : y ≠ (block326S3 : ℝ))
    (hy4ne : y ≠ (block326S4 : ℝ)) :
    0 < block326V y := by
  have hL : (block326RightChunk000L : ℝ) = (block326RightL : ℝ) := by
    norm_num [block326RightChunk000L, block326RightL]
  have hR : (block326RightChunk000R : ℝ) = (block326RightR : ℝ) := by
    norm_num [block326RightChunk000R, block326RightR]
  have hyc : y ∈ Icc (block326RightChunk000L : ℝ) (block326RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block326_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block326_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block326LeftL : ℝ) (block326LeftR : ℝ) →
    y ≠ 0 → y ≠ (block326S1 : ℝ) → y ≠ (block326S2 : ℝ) →
    y ≠ (block326S3 : ℝ) → y ≠ (block326S4 : ℝ) → 0 < block326V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block326RightL : ℝ) (block326RightR : ℝ) →
    y ≠ 0 → y ≠ (block326S1 : ℝ) → y ≠ (block326S2 : ℝ) →
    y ≠ (block326S3 : ℝ) → y ≠ (block326S4 : ℝ) → 0 < block326V y)

theorem block326_reallog_certificate_proof :
    block326_reallog_certificate := by
  exact ⟨block326_left_V_pos, block326_right_V_pos⟩

end Block326
end M1817475
end Erdos1038Lean
