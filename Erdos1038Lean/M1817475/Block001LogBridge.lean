import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block001

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block001

open Set

def block001W1 : Rat := ((3727641881858767 : Rat) / 250000000000000)
def block001W2 : Rat := (0 : Rat)
def block001W3 : Rat := (0 : Rat)
def block001W4 : Rat := ((2482639961852091 : Rat) / 10000000000000000)
def block001S1 : Rat := ((18174751 : Rat) / 10000000)
def block001S2 : Rat := ((511587 : Rat) / 200000)
def block001S3 : Rat := ((107000619 : Rat) / 40000000)
def block001S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block001V (y : ℝ) : ℝ :=
  ratPotential block001W1 block001W2 block001W3 block001W4 block001S1 block001S2 block001S3 block001S4 y

def block001LeftParamsCertificate : Bool :=
  allBoxesSameParams block001LeftBoxes block001W1 block001W2 block001W3 block001W4 block001S1 block001S2 block001S3 block001S4

theorem block001LeftParamsCertificate_eq_true :
    block001LeftParamsCertificate = true := by
  native_decide

theorem block001_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block001LeftL : ℝ) (block001LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block001S1 : ℝ))
    (hy2ne : y ≠ (block001S2 : ℝ))
    (hy3ne : y ≠ (block001S3 : ℝ))
    (hy4ne : y ≠ (block001S4 : ℝ)) :
    0 < block001V y := by
  have hcert := block001LeftCertificate_eq_true
  unfold block001LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block001LeftBoxes) (lo := block001LeftL) (hi := block001LeftR)
    (w1 := block001W1) (w2 := block001W2) (w3 := block001W3) (w4 := block001W4)
    (s1 := block001S1) (s2 := block001S2) (s3 := block001S3) (s4 := block001S4)
    hboxes hcover block001LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block001RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block001RightChunk000 block001W1 block001W2 block001W3 block001W4 block001S1 block001S2 block001S3 block001S4

theorem block001RightChunk000ParamsCertificate_eq_true :
    block001RightChunk000ParamsCertificate = true := by
  native_decide

theorem block001_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block001RightChunk000L : ℝ) (block001RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block001S1 : ℝ))
    (hy2ne : y ≠ (block001S2 : ℝ))
    (hy3ne : y ≠ (block001S3 : ℝ))
    (hy4ne : y ≠ (block001S4 : ℝ)) :
    0 < block001V y := by
  have hcert := block001RightChunk000Certificate_eq_true
  unfold block001RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block001RightChunk000) (lo := block001RightChunk000L) (hi := block001RightChunk000R)
    (w1 := block001W1) (w2 := block001W2) (w3 := block001W3) (w4 := block001W4)
    (s1 := block001S1) (s2 := block001S2) (s3 := block001S3) (s4 := block001S4)
    hboxes hcover block001RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block001_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block001RightL : ℝ) (block001RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block001S1 : ℝ))
    (hy2ne : y ≠ (block001S2 : ℝ))
    (hy3ne : y ≠ (block001S3 : ℝ))
    (hy4ne : y ≠ (block001S4 : ℝ)) :
    0 < block001V y := by
  have hL : (block001RightChunk000L : ℝ) = (block001RightL : ℝ) := by
    norm_num [block001RightChunk000L, block001RightL]
  have hR : (block001RightChunk000R : ℝ) = (block001RightR : ℝ) := by
    norm_num [block001RightChunk000R, block001RightR]
  have hyc : y ∈ Icc (block001RightChunk000L : ℝ) (block001RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block001_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block001_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block001LeftL : ℝ) (block001LeftR : ℝ) →
    y ≠ 0 → y ≠ (block001S1 : ℝ) → y ≠ (block001S2 : ℝ) →
    y ≠ (block001S3 : ℝ) → y ≠ (block001S4 : ℝ) → 0 < block001V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block001RightL : ℝ) (block001RightR : ℝ) →
    y ≠ 0 → y ≠ (block001S1 : ℝ) → y ≠ (block001S2 : ℝ) →
    y ≠ (block001S3 : ℝ) → y ≠ (block001S4 : ℝ) → 0 < block001V y)

theorem block001_reallog_certificate_proof :
    block001_reallog_certificate := by
  exact ⟨block001_left_V_pos, block001_right_V_pos⟩

end Block001
end M1817475
end Erdos1038Lean
