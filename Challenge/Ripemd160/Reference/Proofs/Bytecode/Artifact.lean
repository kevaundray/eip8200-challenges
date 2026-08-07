import Challenge.EvmProof.CertifiedArtifact
import Challenge.Ripemd160.Reference.Bytecode
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# Structural certificate for the frozen RIPEMD-160 artifact

The instruction-boundary list below is generated from the reusable raw-bytecode
disassembler. Its assembly theorem ties every location used by the direct proof
to the exact frozen bytes.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def op (opcode : UInt8) : Instr :=
  match Decode.opcodeOf opcode with
  | some decoded => .op decoded
  | none => .op .INVALID

def referenceRows : Array Challenge.EvmProof.CertifiedArtifact.Entry := #[
  ⟨0, .push 2 27⟩,
  ⟨3, op 0x56⟩,
  ⟨4, op 0x5b⟩,
  ⟨5, .push 4 4294967295⟩,
  ⟨10, op 0x81⟩,
  ⟨11, op 0x83⟩,
  ⟨12, .push 1 32⟩,
  ⟨14, op 0x03⟩,
  ⟨15, op 0x1c⟩,
  ⟨16, op 0x82⟩,
  ⟨17, op 0x84⟩,
  ⟨18, op 0x1b⟩,
  ⟨19, op 0x17⟩,
  ⟨20, op 0x16⟩,
  ⟨21, op 0x92⟩,
  ⟨22, op 0x50⟩,
  ⟨23, op 0x50⟩,
  ⟨24, op 0x50⟩,
  ⟨25, op 0x90⟩,
  ⟨26, op 0x56⟩,
  ⟨27, op 0x5b⟩,
  ⟨28, .push 2 46⟩,
  ⟨31, op 0x56⟩,
  ⟨32, op 0x5b⟩,
  ⟨33, op 0x80⟩,
  ⟨34, .push 1 5⟩,
  ⟨36, op 0x1b⟩,
  ⟨37, .push 1 32⟩,
  ⟨39, op 0x01⟩,
  ⟨40, op 0x51⟩,
  ⟨41, op 0x91⟩,
  ⟨42, op 0x50⟩,
  ⟨43, op 0x50⟩,
  ⟨44, op 0x90⟩,
  ⟨45, op 0x56⟩,
  ⟨46, op 0x5b⟩,
  ⟨47, .push 2 70⟩,
  ⟨50, op 0x56⟩,
  ⟨51, op 0x5b⟩,
  ⟨52, .push 4 4294967295⟩,
  ⟨57, op 0x83⟩,
  ⟨58, op 0x16⟩,
  ⟨59, op 0x82⟩,
  ⟨60, .push 1 5⟩,
  ⟨62, op 0x1b⟩,
  ⟨63, op 0x82⟩,
  ⟨64, op 0x01⟩,
  ⟨65, op 0x52⟩,
  ⟨66, op 0x50⟩,
  ⟨67, op 0x50⟩,
  ⟨68, op 0x50⟩,
  ⟨69, op 0x56⟩,
  ⟨70, op 0x5b⟩,
  ⟨71, .push 2 90⟩,
  ⟨74, op 0x56⟩,
  ⟨75, op 0x5b⟩,
  ⟨76, op 0x80⟩,
  ⟨77, .push 1 5⟩,
  ⟨79, op 0x1b⟩,
  ⟨80, .push 2 672⟩,
  ⟨83, op 0x01⟩,
  ⟨84, op 0x51⟩,
  ⟨85, op 0x91⟩,
  ⟨86, op 0x50⟩,
  ⟨87, op 0x50⟩,
  ⟨88, op 0x90⟩,
  ⟨89, op 0x56⟩,
  ⟨90, op 0x5b⟩,
  ⟨91, .push 2 115⟩,
  ⟨94, op 0x56⟩,
  ⟨95, op 0x5b⟩,
  ⟨96, .push 4 4294967295⟩,
  ⟨101, op 0x82⟩,
  ⟨102, op 0x16⟩,
  ⟨103, op 0x81⟩,
  ⟨104, .push 1 5⟩,
  ⟨106, op 0x1b⟩,
  ⟨107, .push 2 672⟩,
  ⟨110, op 0x01⟩,
  ⟨111, op 0x52⟩,
  ⟨112, op 0x50⟩,
  ⟨113, op 0x50⟩,
  ⟨114, op 0x56⟩,
  ⟨115, op 0x5b⟩,
  ⟨116, .push 2 142⟩,
  ⟨119, op 0x56⟩,
  ⟨120, op 0x5b⟩,
  ⟨121, op 0x81⟩,
  ⟨122, .push 1 5⟩,
  ⟨124, op 0x1c⟩,
  ⟨125, .push 1 5⟩,
  ⟨127, op 0x1b⟩,
  ⟨128, op 0x81⟩,
  ⟨129, op 0x01⟩,
  ⟨130, op 0x51⟩,
  ⟨131, .push 1 31⟩,
  ⟨133, op 0x83⟩,
  ⟨134, op 0x16⟩,
  ⟨135, op 0x1a⟩,
  ⟨136, op 0x92⟩,
  ⟨137, op 0x50⟩,
  ⟨138, op 0x50⟩,
  ⟨139, op 0x50⟩,
  ⟨140, op 0x90⟩,
  ⟨141, op 0x56⟩,
  ⟨142, op 0x5b⟩,
  ⟨143, .push 2 271⟩,
  ⟨146, op 0x56⟩,
  ⟨147, op 0x5b⟩,
  ⟨148, op 0x80⟩,
  ⟨149, op 0x80⟩,
  ⟨150, .push 0 0⟩,
  ⟨151, op 0x14⟩,
  ⟨152, op 0x15⟩,
  ⟨153, .push 2 169⟩,
  ⟨156, op 0x57⟩,
  ⟨157, op 0x50⟩,
  ⟨158, op 0x83⟩,
  ⟨159, op 0x83⟩,
  ⟨160, op 0x83⟩,
  ⟨161, op 0x18⟩,
  ⟨162, op 0x18⟩,
  ⟨163, op 0x94⟩,
  ⟨164, op 0x50⟩,
  ⟨165, .push 2 264⟩,
  ⟨168, op 0x56⟩,
  ⟨169, op 0x5b⟩,
  ⟨170, op 0x80⟩,
  ⟨171, .push 1 1⟩,
  ⟨173, op 0x14⟩,
  ⟨174, op 0x15⟩,
  ⟨175, .push 2 194⟩,
  ⟨178, op 0x57⟩,
  ⟨179, op 0x50⟩,
  ⟨180, op 0x83⟩,
  ⟨181, op 0x82⟩,
  ⟨182, op 0x19⟩,
  ⟨183, op 0x16⟩,
  ⟨184, op 0x83⟩,
  ⟨185, op 0x83⟩,
  ⟨186, op 0x16⟩,
  ⟨187, op 0x17⟩,
  ⟨188, op 0x94⟩,
  ⟨189, op 0x50⟩,
  ⟨190, .push 2 264⟩,
  ⟨193, op 0x56⟩,
  ⟨194, op 0x5b⟩,
  ⟨195, op 0x80⟩,
  ⟨196, .push 1 2⟩,
  ⟨198, op 0x14⟩,
  ⟨199, op 0x15⟩,
  ⟨200, .push 2 223⟩,
  ⟨203, op 0x57⟩,
  ⟨204, op 0x50⟩,
  ⟨205, .push 4 4294967295⟩,
  ⟨210, op 0x84⟩,
  ⟨211, op 0x84⟩,
  ⟨212, op 0x19⟩,
  ⟨213, op 0x84⟩,
  ⟨214, op 0x17⟩,
  ⟨215, op 0x18⟩,
  ⟨216, op 0x16⟩,
  ⟨217, op 0x94⟩,
  ⟨218, op 0x50⟩,
  ⟨219, .push 2 264⟩,
  ⟨222, op 0x56⟩,
  ⟨223, op 0x5b⟩,
  ⟨224, op 0x80⟩,
  ⟨225, .push 1 3⟩,
  ⟨227, op 0x14⟩,
  ⟨228, op 0x15⟩,
  ⟨229, .push 2 248⟩,
  ⟨232, op 0x57⟩,
  ⟨233, op 0x50⟩,
  ⟨234, op 0x83⟩,
  ⟨235, op 0x19⟩,
  ⟨236, op 0x83⟩,
  ⟨237, op 0x16⟩,
  ⟨238, op 0x84⟩,
  ⟨239, op 0x83⟩,
  ⟨240, op 0x16⟩,
  ⟨241, op 0x17⟩,
  ⟨242, op 0x94⟩,
  ⟨243, op 0x50⟩,
  ⟨244, .push 2 264⟩,
  ⟨247, op 0x56⟩,
  ⟨248, op 0x5b⟩,
  ⟨249, op 0x50⟩,
  ⟨250, .push 4 4294967295⟩,
  ⟨255, op 0x84⟩,
  ⟨256, op 0x19⟩,
  ⟨257, op 0x84⟩,
  ⟨258, op 0x17⟩,
  ⟨259, op 0x83⟩,
  ⟨260, op 0x18⟩,
  ⟨261, op 0x16⟩,
  ⟨262, op 0x94⟩,
  ⟨263, op 0x50⟩,
  ⟨264, op 0x5b⟩,
  ⟨265, op 0x50⟩,
  ⟨266, op 0x50⟩,
  ⟨267, op 0x50⟩,
  ⟨268, op 0x50⟩,
  ⟨269, op 0x90⟩,
  ⟨270, op 0x56⟩,
  ⟨271, op 0x5b⟩,
  ⟨272, .push 2 434⟩,
  ⟨275, op 0x56⟩,
  ⟨276, op 0x5b⟩,
  ⟨277, op 0x80⟩,
  ⟨278, op 0x51⟩,
  ⟨279, .push 1 32⟩,
  ⟨281, op 0x82⟩,
  ⟨282, op 0x01⟩,
  ⟨283, op 0x51⟩,
  ⟨284, .push 1 64⟩,
  ⟨286, op 0x83⟩,
  ⟨287, op 0x01⟩,
  ⟨288, op 0x51⟩,
  ⟨289, .push 1 96⟩,
  ⟨291, op 0x84⟩,
  ⟨292, op 0x01⟩,
  ⟨293, op 0x51⟩,
  ⟨294, .push 1 128⟩,
  ⟨296, op 0x85⟩,
  ⟨297, op 0x01⟩,
  ⟨298, op 0x51⟩,
  ⟨299, .push 4 4294967295⟩,
  ⟨304, op 0x8a⟩,
  ⟨305, .push 2 314⟩,
  ⟨308, .push 0 0⟩,
  ⟨309, op 0x8b⟩,
  ⟨310, .push 2 75⟩,
  ⟨313, op 0x56⟩,
  ⟨314, op 0x5b⟩,
  ⟨315, .push 2 327⟩,
  ⟨318, .push 0 0⟩,
  ⟨319, op 0x86⟩,
  ⟨320, op 0x88⟩,
  ⟨321, op 0x8a⟩,
  ⟨322, op 0x8e⟩,
  ⟨323, .push 2 147⟩,
  ⟨326, op 0x56⟩,
  ⟨327, op 0x5b⟩,
  ⟨328, op 0x88⟩,
  ⟨329, op 0x01⟩,
  ⟨330, op 0x01⟩,
  ⟨331, op 0x01⟩,
  ⟨332, op 0x16⟩,
  ⟨333, .push 4 4294967295⟩,
  ⟨338, op 0x82⟩,
  ⟨339, .push 2 349⟩,
  ⟨342, .push 0 0⟩,
  ⟨343, op 0x8d⟩,
  ⟨344, op 0x85⟩,
  ⟨345, .push 2 4⟩,
  ⟨348, op 0x56⟩,
  ⟨349, op 0x5b⟩,
  ⟨350, op 0x01⟩,
  ⟨351, op 0x16⟩,
  ⟨352, op 0x90⟩,
  ⟨353, op 0x50⟩,
  ⟨354, .push 4 4294967295⟩,
  ⟨359, op 0x82⟩,
  ⟨360, op 0x16⟩,
  ⟨361, op 0x87⟩,
  ⟨362, op 0x52⟩,
  ⟨363, .push 4 4294967295⟩,
  ⟨368, op 0x83⟩,
  ⟨369, op 0x16⟩,
  ⟨370, .push 1 128⟩,
  ⟨372, op 0x88⟩,
  ⟨373, op 0x01⟩,
  ⟨374, op 0x52⟩,
  ⟨375, .push 2 397⟩,
  ⟨378, .push 2 389⟩,
  ⟨381, .push 0 0⟩,
  ⟨382, .push 1 10⟩,
  ⟨384, op 0x87⟩,
  ⟨385, .push 2 4⟩,
  ⟨388, op 0x56⟩,
  ⟨389, op 0x5b⟩,
  ⟨390, .push 1 3⟩,
  ⟨392, op 0x89⟩,
  ⟨393, .push 2 51⟩,
  ⟨396, op 0x56⟩,
  ⟨397, op 0x5b⟩,
  ⟨398, .push 4 4294967295⟩,
  ⟨403, op 0x85⟩,
  ⟨404, op 0x16⟩,
  ⟨405, .push 1 64⟩,
  ⟨407, op 0x88⟩,
  ⟨408, op 0x01⟩,
  ⟨409, op 0x52⟩,
  ⟨410, .push 4 4294967295⟩,
  ⟨415, op 0x81⟩,
  ⟨416, op 0x16⟩,
  ⟨417, .push 1 32⟩,
  ⟨419, op 0x88⟩,
  ⟨420, op 0x01⟩,
  ⟨421, op 0x52⟩,
  ⟨422, op 0x50⟩,
  ⟨423, op 0x50⟩,
  ⟨424, op 0x50⟩,
  ⟨425, op 0x50⟩,
  ⟨426, op 0x50⟩,
  ⟨427, op 0x50⟩,
  ⟨428, op 0x50⟩,
  ⟨429, op 0x50⟩,
  ⟨430, op 0x50⟩,
  ⟨431, op 0x50⟩,
  ⟨432, op 0x50⟩,
  ⟨433, op 0x56⟩,
  ⟨434, op 0x5b⟩,
  ⟨435, .push 2 475⟩,
  ⟨438, op 0x56⟩,
  ⟨439, op 0x5b⟩,
  ⟨440, op 0x80⟩,
  ⟨441, op 0x51⟩,
  ⟨442, op 0x80⟩,
  ⟨443, .push 1 3⟩,
  ⟨445, op 0x1a⟩,
  ⟨446, .push 1 24⟩,
  ⟨448, op 0x1b⟩,
  ⟨449, op 0x81⟩,
  ⟨450, .push 1 2⟩,
  ⟨452, op 0x1a⟩,
  ⟨453, .push 1 16⟩,
  ⟨455, op 0x1b⟩,
  ⟨456, op 0x17⟩,
  ⟨457, op 0x81⟩,
  ⟨458, .push 1 1⟩,
  ⟨460, op 0x1a⟩,
  ⟨461, .push 1 8⟩,
  ⟨463, op 0x1b⟩,
  ⟨464, op 0x82⟩,
  ⟨465, .push 0 0⟩,
  ⟨466, op 0x1a⟩,
  ⟨467, op 0x17⟩,
  ⟨468, op 0x17⟩,
  ⟨469, op 0x92⟩,
  ⟨470, op 0x50⟩,
  ⟨471, op 0x50⟩,
  ⟨472, op 0x50⟩,
  ⟨473, op 0x90⟩,
  ⟨474, op 0x56⟩,
  ⟨475, op 0x5b⟩,
  ⟨476, .push 2 561⟩,
  ⟨479, op 0x56⟩,
  ⟨480, op 0x5b⟩,
  ⟨481, op 0x36⟩,
  ⟨482, .push 1 72⟩,
  ⟨484, op 0x81⟩,
  ⟨485, op 0x01⟩,
  ⟨486, .push 1 6⟩,
  ⟨488, op 0x1c⟩,
  ⟨489, .push 1 6⟩,
  ⟨491, op 0x1b⟩,
  ⟨492, op 0x91⟩,
  ⟨493, op 0x50⟩,
  ⟨494, op 0x80⟩,
  ⟨495, .push 0 0⟩,
  ⟨496, .push 2 2048⟩,
  ⟨499, op 0x37⟩,
  ⟨500, .push 1 128⟩,
  ⟨502, op 0x81⟩,
  ⟨503, .push 2 2048⟩,
  ⟨506, op 0x01⟩,
  ⟨507, op 0x53⟩,
  ⟨508, op 0x80⟩,
  ⟨509, .push 1 3⟩,
  ⟨511, op 0x1b⟩,
  ⟨512, .push 1 8⟩,
  ⟨514, op 0x83⟩,
  ⟨515, op 0x03⟩,
  ⟨516, .push 2 2048⟩,
  ⟨519, op 0x01⟩,
  ⟨520, .push 0 0⟩,
  ⟨521, op 0x5b⟩,
  ⟨522, .push 1 8⟩,
  ⟨524, op 0x81⟩,
  ⟨525, op 0x10⟩,
  ⟨526, op 0x15⟩,
  ⟨527, .push 2 554⟩,
  ⟨530, op 0x57⟩,
  ⟨531, .push 1 255⟩,
  ⟨533, op 0x83⟩,
  ⟨534, op 0x82⟩,
  ⟨535, .push 1 3⟩,
  ⟨537, op 0x1b⟩,
  ⟨538, op 0x1c⟩,
  ⟨539, op 0x16⟩,
  ⟨540, op 0x81⟩,
  ⟨541, op 0x83⟩,
  ⟨542, op 0x01⟩,
  ⟨543, op 0x53⟩,
  ⟨544, .push 1 1⟩,
  ⟨546, op 0x81⟩,
  ⟨547, op 0x01⟩,
  ⟨548, op 0x90⟩,
  ⟨549, op 0x50⟩,
  ⟨550, .push 2 521⟩,
  ⟨553, op 0x56⟩,
  ⟨554, op 0x5b⟩,
  ⟨555, op 0x50⟩,
  ⟨556, op 0x50⟩,
  ⟨557, op 0x50⟩,
  ⟨558, op 0x50⟩,
  ⟨559, op 0x90⟩,
  ⟨560, op 0x56⟩,
  ⟨561, op 0x5b⟩,
  ⟨562, .push 2 616⟩,
  ⟨565, op 0x56⟩,
  ⟨566, op 0x5b⟩,
  ⟨567, .push 0 0⟩,
  ⟨568, op 0x5b⟩,
  ⟨569, .push 1 16⟩,
  ⟨571, op 0x81⟩,
  ⟨572, op 0x10⟩,
  ⟨573, op 0x15⟩,
  ⟨574, .push 2 612⟩,
  ⟨577, op 0x57⟩,
  ⟨578, .push 2 601⟩,
  ⟨581, .push 2 595⟩,
  ⟨584, .push 0 0⟩,
  ⟨585, op 0x83⟩,
  ⟨586, .push 1 2⟩,
  ⟨588, op 0x1b⟩,
  ⟨589, op 0x85⟩,
  ⟨590, op 0x01⟩,
  ⟨591, .push 2 439⟩,
  ⟨594, op 0x56⟩,
  ⟨595, op 0x5b⟩,
  ⟨596, op 0x82⟩,
  ⟨597, .push 2 95⟩,
  ⟨600, op 0x56⟩,
  ⟨601, op 0x5b⟩,
  ⟨602, .push 1 1⟩,
  ⟨604, op 0x81⟩,
  ⟨605, op 0x01⟩,
  ⟨606, op 0x90⟩,
  ⟨607, op 0x50⟩,
  ⟨608, .push 2 568⟩,
  ⟨611, op 0x56⟩,
  ⟨612, op 0x5b⟩,
  ⟨613, op 0x50⟩,
  ⟨614, op 0x50⟩,
  ⟨615, op 0x56⟩,
  ⟨616, op 0x5b⟩,
  ⟨617, .push 2 961⟩,
  ⟨620, op 0x56⟩,
  ⟨621, op 0x5b⟩,
  ⟨622, .push 2 630⟩,
  ⟨625, op 0x81⟩,
  ⟨626, .push 2 566⟩,
  ⟨629, op 0x56⟩,
  ⟨630, op 0x5b⟩,
  ⟨631, .push 1 160⟩,
  ⟨633, .push 1 32⟩,
  ⟨635, .push 1 192⟩,
  ⟨637, op 0x5e⟩,
  ⟨638, .push 1 160⟩,
  ⟨640, .push 1 32⟩,
  ⟨642, .push 2 352⟩,
  ⟨645, op 0x5e⟩,
  ⟨646, .push 1 160⟩,
  ⟨648, .push 1 32⟩,
  ⟨650, .push 2 512⟩,
  ⟨653, op 0x5e⟩,
  ⟨654, .push 0 0⟩,
  ⟨655, op 0x5b⟩,
  ⟨656, .push 1 80⟩,
  ⟨658, op 0x81⟩,
  ⟨659, op 0x10⟩,
  ⟨660, op 0x15⟩,
  ⟨661, .push 2 726⟩,
  ⟨664, op 0x57⟩,
  ⟨665, op 0x80⟩,
  ⟨666, .push 1 4⟩,
  ⟨668, op 0x1c⟩,
  ⟨669, .push 2 714⟩,
  ⟨672, op 0x81⟩,
  ⟨673, .push 1 5⟩,
  ⟨675, op 0x1b⟩,
  ⟨676, .push 2 1568⟩,
  ⟨679, op 0x01⟩,
  ⟨680, op 0x51⟩,
  ⟨681, .push 2 693⟩,
  ⟨684, .push 0 0⟩,
  ⟨685, op 0x85⟩,
  ⟨686, .push 2 1376⟩,
  ⟨689, .push 2 120⟩,
  ⟨692, op 0x56⟩,
  ⟨693, op 0x5b⟩,
  ⟨694, .push 2 706⟩,
  ⟨697, .push 0 0⟩,
  ⟨698, op 0x86⟩,
  ⟨699, .push 2 1184⟩,
  ⟨702, .push 2 120⟩,
  ⟨705, op 0x56⟩,
  ⟨706, op 0x5b⟩,
  ⟨707, op 0x84⟩,
  ⟨708, .push 1 192⟩,
  ⟨710, .push 2 276⟩,
  ⟨713, op 0x56⟩,
  ⟨714, op 0x5b⟩,
  ⟨715, op 0x50⟩,
  ⟨716, .push 1 1⟩,
  ⟨718, op 0x81⟩,
  ⟨719, op 0x01⟩,
  ⟨720, op 0x90⟩,
  ⟨721, op 0x50⟩,
  ⟨722, .push 2 655⟩,
  ⟨725, op 0x56⟩,
  ⟨726, op 0x5b⟩,
  ⟨727, op 0x50⟩,
  ⟨728, .push 0 0⟩,
  ⟨729, op 0x5b⟩,
  ⟨730, .push 1 80⟩,
  ⟨732, op 0x81⟩,
  ⟨733, op 0x10⟩,
  ⟨734, op 0x15⟩,
  ⟨735, .push 2 804⟩,
  ⟨738, op 0x57⟩,
  ⟨739, op 0x80⟩,
  ⟨740, .push 1 4⟩,
  ⟨742, op 0x1c⟩,
  ⟨743, .push 2 792⟩,
  ⟨746, op 0x81⟩,
  ⟨747, .push 1 5⟩,
  ⟨749, op 0x1b⟩,
  ⟨750, .push 2 1728⟩,
  ⟨753, op 0x01⟩,
  ⟨754, op 0x51⟩,
  ⟨755, .push 2 767⟩,
  ⟨758, .push 0 0⟩,
  ⟨759, op 0x85⟩,
  ⟨760, .push 2 1472⟩,
  ⟨763, .push 2 120⟩,
  ⟨766, op 0x56⟩,
  ⟨767, op 0x5b⟩,
  ⟨768, .push 2 780⟩,
  ⟨771, .push 0 0⟩,
  ⟨772, op 0x86⟩,
  ⟨773, .push 2 1280⟩,
  ⟨776, .push 2 120⟩,
  ⟨779, op 0x56⟩,
  ⟨780, op 0x5b⟩,
  ⟨781, op 0x84⟩,
  ⟨782, .push 1 4⟩,
  ⟨784, op 0x03⟩,
  ⟨785, .push 2 352⟩,
  ⟨788, .push 2 276⟩,
  ⟨791, op 0x56⟩,
  ⟨792, op 0x5b⟩,
  ⟨793, op 0x50⟩,
  ⟨794, .push 1 1⟩,
  ⟨796, op 0x81⟩,
  ⟨797, op 0x01⟩,
  ⟨798, op 0x90⟩,
  ⟨799, op 0x50⟩,
  ⟨800, .push 2 729⟩,
  ⟨803, op 0x56⟩,
  ⟨804, op 0x5b⟩,
  ⟨805, op 0x50⟩,
  ⟨806, .push 4 4294967295⟩,
  ⟨811, .push 2 448⟩,
  ⟨814, op 0x51⟩,
  ⟨815, .push 2 256⟩,
  ⟨818, op 0x51⟩,
  ⟨819, .push 2 544⟩,
  ⟨822, op 0x51⟩,
  ⟨823, op 0x01⟩,
  ⟨824, op 0x01⟩,
  ⟨825, op 0x16⟩,
  ⟨826, .push 4 4294967295⟩,
  ⟨831, .push 2 480⟩,
  ⟨834, op 0x51⟩,
  ⟨835, .push 2 288⟩,
  ⟨838, op 0x51⟩,
  ⟨839, .push 2 576⟩,
  ⟨842, op 0x51⟩,
  ⟨843, op 0x01⟩,
  ⟨844, op 0x01⟩,
  ⟨845, op 0x16⟩,
  ⟨846, .push 4 4294967295⟩,
  ⟨851, op 0x81⟩,
  ⟨852, op 0x16⟩,
  ⟨853, .push 1 64⟩,
  ⟨855, op 0x52⟩,
  ⟨856, .push 4 4294967295⟩,
  ⟨861, .push 2 352⟩,
  ⟨864, op 0x51⟩,
  ⟨865, .push 2 320⟩,
  ⟨868, op 0x51⟩,
  ⟨869, .push 2 608⟩,
  ⟨872, op 0x51⟩,
  ⟨873, op 0x01⟩,
  ⟨874, op 0x01⟩,
  ⟨875, op 0x16⟩,
  ⟨876, .push 4 4294967295⟩,
  ⟨881, op 0x81⟩,
  ⟨882, op 0x16⟩,
  ⟨883, .push 1 96⟩,
  ⟨885, op 0x52⟩,
  ⟨886, .push 4 4294967295⟩,
  ⟨891, .push 2 384⟩,
  ⟨894, op 0x51⟩,
  ⟨895, .push 1 192⟩,
  ⟨897, op 0x51⟩,
  ⟨898, .push 2 640⟩,
  ⟨901, op 0x51⟩,
  ⟨902, op 0x01⟩,
  ⟨903, op 0x01⟩,
  ⟨904, op 0x16⟩,
  ⟨905, .push 4 4294967295⟩,
  ⟨910, op 0x81⟩,
  ⟨911, op 0x16⟩,
  ⟨912, .push 1 128⟩,
  ⟨914, op 0x52⟩,
  ⟨915, .push 4 4294967295⟩,
  ⟨920, .push 2 416⟩,
  ⟨923, op 0x51⟩,
  ⟨924, .push 1 224⟩,
  ⟨926, op 0x51⟩,
  ⟨927, .push 2 512⟩,
  ⟨930, op 0x51⟩,
  ⟨931, op 0x01⟩,
  ⟨932, op 0x01⟩,
  ⟨933, op 0x16⟩,
  ⟨934, .push 4 4294967295⟩,
  ⟨939, op 0x81⟩,
  ⟨940, op 0x16⟩,
  ⟨941, .push 1 160⟩,
  ⟨943, op 0x52⟩,
  ⟨944, .push 4 4294967295⟩,
  ⟨949, op 0x85⟩,
  ⟨950, op 0x16⟩,
  ⟨951, .push 1 32⟩,
  ⟨953, op 0x52⟩,
  ⟨954, op 0x50⟩,
  ⟨955, op 0x50⟩,
  ⟨956, op 0x50⟩,
  ⟨957, op 0x50⟩,
  ⟨958, op 0x50⟩,
  ⟨959, op 0x50⟩,
  ⟨960, op 0x56⟩,
  ⟨961, op 0x5b⟩,
  ⟨962, .push 2 1006⟩,
  ⟨965, op 0x56⟩,
  ⟨966, op 0x5b⟩,
  ⟨967, .push 0 0⟩,
  ⟨968, op 0x5b⟩,
  ⟨969, .push 1 4⟩,
  ⟨971, op 0x81⟩,
  ⟨972, op 0x10⟩,
  ⟨973, op 0x15⟩,
  ⟨974, .push 2 1001⟩,
  ⟨977, op 0x57⟩,
  ⟨978, .push 1 255⟩,
  ⟨980, op 0x83⟩,
  ⟨981, op 0x82⟩,
  ⟨982, .push 1 3⟩,
  ⟨984, op 0x1b⟩,
  ⟨985, op 0x1c⟩,
  ⟨986, op 0x16⟩,
  ⟨987, op 0x81⟩,
  ⟨988, op 0x83⟩,
  ⟨989, op 0x01⟩,
  ⟨990, op 0x53⟩,
  ⟨991, .push 1 1⟩,
  ⟨993, op 0x81⟩,
  ⟨994, op 0x01⟩,
  ⟨995, op 0x90⟩,
  ⟨996, op 0x50⟩,
  ⟨997, .push 2 968⟩,
  ⟨1000, op 0x56⟩,
  ⟨1001, op 0x5b⟩,
  ⟨1002, op 0x50⟩,
  ⟨1003, op 0x50⟩,
  ⟨1004, op 0x50⟩,
  ⟨1005, op 0x56⟩,
  ⟨1006, op 0x5b⟩,
  ⟨1007, .push 31 1780731860627700044960722568376592188711674974810043212252563479055960840⟩,
  ⟨1039, .push 2 1184⟩,
  ⟨1042, op 0x52⟩,
  ⟨1043, .push 32 1374703749640218873849524064026661036561295975619335768036000015621818746370⟩,
  ⟨1076, .push 2 1216⟩,
  ⟨1079, op 0x52⟩,
  ⟨1080, .push 32 1809286146446445343010337679715913357291520642540487409382712519614204477440⟩,
  ⟨1113, .push 2 1248⟩,
  ⟨1116, op 0x52⟩,
  ⟨1117, .push 32 2286348414996307935469207465186628553155355030353023797310855598864584999170⟩,
  ⟨1150, .push 2 1280⟩,
  ⟨1153, op 0x52⟩,
  ⟨1154, .push 32 6793533947442029545286681365244130742947859423983440781638017424580845963790⟩,
  ⟨1187, .push 2 1312⟩,
  ⟨1190, op 0x52⟩,
  ⟨1191, .push 32 5454326014381509071620663843103927214778145566039445656282506490595801825280⟩,
  ⟨1224, .push 2 1344⟩,
  ⟨1227, op 0x52⟩,
  ⟨1228, .push 32 5000281043567253289773844389228683908720941172611121566642559091978571025676⟩,
  ⟨1261, .push 2 1376⟩,
  ⟨1264, op 0x52⟩,
  ⟨1265, .push 32 4998451946933852135137276647445154408072640462072745561656555001729660617996⟩,
  ⟨1298, .push 2 1408⟩,
  ⟨1301, op 0x52⟩,
  ⟨1302, .push 32 4097353149147406276549177442451244923784709130172834976461593227075946283008⟩,
  ⟨1335, .push 2 1440⟩,
  ⟨1338, op 0x52⟩,
  ⟨1339, .push 32 3634466825900925589093651101374881051901026410458987220032629834781140389131⟩,
  ⟨1372, .push 2 1472⟩,
  ⟨1375, op 0x52⟩,
  ⟨1376, .push 32 4083287390302437702768465126624575726298108573653391417181074648310269415176⟩,
  ⟨1409, .push 2 1504⟩,
  ⟨1412, op 0x52⟩,
  ⟨1413, .push 32 3627420088851531435467691758328083203359072412578514691593700216701345333248⟩,
  ⟨1446, .push 2 1536⟩,
  ⟨1449, op 0x52⟩,
  ⟨1450, .push 0 0⟩,
  ⟨1451, .push 2 1568⟩,
  ⟨1454, op 0x52⟩,
  ⟨1455, .push 4 1518500249⟩,
  ⟨1460, .push 2 1600⟩,
  ⟨1463, op 0x52⟩,
  ⟨1464, .push 4 1859775393⟩,
  ⟨1469, .push 2 1632⟩,
  ⟨1472, op 0x52⟩,
  ⟨1473, .push 4 2400959708⟩,
  ⟨1478, .push 2 1664⟩,
  ⟨1481, op 0x52⟩,
  ⟨1482, .push 4 2840853838⟩,
  ⟨1487, .push 2 1696⟩,
  ⟨1490, op 0x52⟩,
  ⟨1491, .push 4 1352829926⟩,
  ⟨1496, .push 2 1728⟩,
  ⟨1499, op 0x52⟩,
  ⟨1500, .push 4 1548603684⟩,
  ⟨1505, .push 2 1760⟩,
  ⟨1508, op 0x52⟩,
  ⟨1509, .push 4 1836072691⟩,
  ⟨1514, .push 2 1792⟩,
  ⟨1517, op 0x52⟩,
  ⟨1518, .push 4 2053994217⟩,
  ⟨1523, .push 2 1824⟩,
  ⟨1526, op 0x52⟩,
  ⟨1527, .push 0 0⟩,
  ⟨1528, .push 2 1856⟩,
  ⟨1531, op 0x52⟩,
  ⟨1532, .push 4 1732584193⟩,
  ⟨1537, .push 1 32⟩,
  ⟨1539, op 0x52⟩,
  ⟨1540, .push 4 4023233417⟩,
  ⟨1545, .push 1 64⟩,
  ⟨1547, op 0x52⟩,
  ⟨1548, .push 4 2562383102⟩,
  ⟨1553, .push 1 96⟩,
  ⟨1555, op 0x52⟩,
  ⟨1556, .push 4 271733878⟩,
  ⟨1561, .push 1 128⟩,
  ⟨1563, op 0x52⟩,
  ⟨1564, .push 4 3285377520⟩,
  ⟨1569, .push 1 160⟩,
  ⟨1571, op 0x52⟩,
  ⟨1572, .push 2 1580⟩,
  ⟨1575, .push 0 0⟩,
  ⟨1576, .push 2 480⟩,
  ⟨1579, op 0x56⟩,
  ⟨1580, op 0x5b⟩,
  ⟨1581, .push 0 0⟩,
  ⟨1582, op 0x5b⟩,
  ⟨1583, op 0x81⟩,
  ⟨1584, op 0x81⟩,
  ⟨1585, op 0x10⟩,
  ⟨1586, op 0x15⟩,
  ⟨1587, .push 2 1614⟩,
  ⟨1590, op 0x57⟩,
  ⟨1591, .push 2 1603⟩,
  ⟨1594, op 0x81⟩,
  ⟨1595, .push 2 2048⟩,
  ⟨1598, op 0x01⟩,
  ⟨1599, .push 2 621⟩,
  ⟨1602, op 0x56⟩,
  ⟨1603, op 0x5b⟩,
  ⟨1604, .push 1 64⟩,
  ⟨1606, op 0x81⟩,
  ⟨1607, op 0x01⟩,
  ⟨1608, op 0x90⟩,
  ⟨1609, op 0x50⟩,
  ⟨1610, .push 2 1582⟩,
  ⟨1613, op 0x56⟩,
  ⟨1614, op 0x5b⟩,
  ⟨1615, op 0x50⟩,
  ⟨1616, .push 0 0⟩,
  ⟨1617, .push 0 0⟩,
  ⟨1618, op 0x52⟩,
  ⟨1619, .push 0 0⟩,
  ⟨1620, op 0x5b⟩,
  ⟨1621, .push 1 5⟩,
  ⟨1623, op 0x81⟩,
  ⟨1624, op 0x10⟩,
  ⟨1625, op 0x15⟩,
  ⟨1626, .push 2 1665⟩,
  ⟨1629, op 0x57⟩,
  ⟨1630, .push 2 1654⟩,
  ⟨1633, .push 2 1642⟩,
  ⟨1636, .push 0 0⟩,
  ⟨1637, op 0x83⟩,
  ⟨1638, .push 2 32⟩,
  ⟨1641, op 0x56⟩,
  ⟨1642, op 0x5b⟩,
  ⟨1643, op 0x82⟩,
  ⟨1644, .push 1 2⟩,
  ⟨1646, op 0x1b⟩,
  ⟨1647, .push 1 12⟩,
  ⟨1649, op 0x01⟩,
  ⟨1650, .push 2 966⟩,
  ⟨1653, op 0x56⟩,
  ⟨1654, op 0x5b⟩,
  ⟨1655, .push 1 1⟩,
  ⟨1657, op 0x81⟩,
  ⟨1658, op 0x01⟩,
  ⟨1659, op 0x90⟩,
  ⟨1660, op 0x50⟩,
  ⟨1661, .push 2 1620⟩,
  ⟨1664, op 0x56⟩,
  ⟨1665, op 0x5b⟩,
  ⟨1666, op 0x50⟩,
  ⟨1667, .push 1 32⟩,
  ⟨1669, .push 0 0⟩,
  ⟨1670, op 0xf3⟩,
]

def referenceInstructions : List Instr :=
  Challenge.EvmProof.CertifiedArtifact.instructions referenceRows

theorem referenceInstructions_count : referenceInstructions.length = 831 := by
  decide

theorem assemble_referenceInstructions :
    assemble referenceInstructions = referenceBytecode := by
  apply ByteArray.ext
  simp (config := { maxSteps := 1000000 })
    [assemble, assembleBytes, referenceInstructions, referenceBytecode,
    referenceBytes]
  all_goals decide

theorem referenceRows_valid :
    Challenge.EvmProof.CertifiedArtifact.Table.Valid
      .Osaka referenceBytecode referenceRows := by
  refine ⟨assemble_referenceInstructions, ?_, ?_⟩
  · decide
  · decide

def referenceCertifiedArtifact :
    Challenge.EvmProof.CertifiedArtifact .Osaka referenceBytecode :=
  Challenge.EvmProof.CertifiedArtifact.certify referenceRows referenceRows_valid

private def rowIndex (index : Fin 831) : Fin referenceRows.size :=
  ⟨index, by
    change index.val < 831
    exact index.isLt⟩

theorem entryDecoder_0 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨0, .push 2 27⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 0)
    ⟨0, .push 2 27⟩ (by rfl)

theorem entryDecoder_1 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨3, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 1)
    ⟨3, .op .JUMP⟩ (by rfl)

theorem entryDecoder_20 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨27, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 20)
    ⟨27, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_21 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨28, .push 2 46⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 21)
    ⟨28, .push 2 46⟩ (by rfl)

theorem entryDecoder_22 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨31, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 22)
    ⟨31, .op .JUMP⟩ (by rfl)

theorem entryDecoder_35 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨46, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 35)
    ⟨46, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_36 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨47, .push 2 70⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 36)
    ⟨47, .push 2 70⟩ (by rfl)

theorem entryDecoder_37 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨50, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 37)
    ⟨50, .op .JUMP⟩ (by rfl)

theorem entryDecoder_52 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨70, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 52)
    ⟨70, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_53 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨71, .push 2 90⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 53)
    ⟨71, .push 2 90⟩ (by rfl)

theorem entryDecoder_54 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨74, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 54)
    ⟨74, .op .JUMP⟩ (by rfl)

theorem entryDecoder_67 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨90, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 67)
    ⟨90, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_68 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨91, .push 2 115⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 68)
    ⟨91, .push 2 115⟩ (by rfl)

theorem entryDecoder_69 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨94, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 69)
    ⟨94, .op .JUMP⟩ (by rfl)

theorem entryDecoder_83 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨115, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 83)
    ⟨115, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_84 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨116, .push 2 142⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 84)
    ⟨116, .push 2 142⟩ (by rfl)

theorem entryDecoder_85 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨119, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 85)
    ⟨119, .op .JUMP⟩ (by rfl)

theorem entryDecoder_105 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨142, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 105)
    ⟨142, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_106 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨143, .push 2 271⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 106)
    ⟨143, .push 2 271⟩ (by rfl)

theorem entryDecoder_107 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨146, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 107)
    ⟨146, .op .JUMP⟩ (by rfl)

theorem entryDecoder_205 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨271, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 205)
    ⟨271, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_206 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨272, .push 2 434⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 206)
    ⟨272, .push 2 434⟩ (by rfl)

theorem entryDecoder_207 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨275, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 207)
    ⟨275, .op .JUMP⟩ (by rfl)

theorem entryDecoder_313 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨434, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 313)
    ⟨434, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_314 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨435, .push 2 475⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 314)
    ⟨435, .push 2 475⟩ (by rfl)

theorem entryDecoder_315 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨438, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 315)
    ⟨438, .op .JUMP⟩ (by rfl)

theorem entryDecoder_346 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨475, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 346)
    ⟨475, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_347 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨476, .push 2 561⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 347)
    ⟨476, .push 2 561⟩ (by rfl)

theorem entryDecoder_348 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨479, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 348)
    ⟨479, .op .JUMP⟩ (by rfl)

theorem entryDecoder_410 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨561, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 410)
    ⟨561, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_411 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨562, .push 2 616⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 411)
    ⟨562, .push 2 616⟩ (by rfl)

theorem entryDecoder_412 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨565, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 412)
    ⟨565, .op .JUMP⟩ (by rfl)

theorem entryDecoder_448 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨616, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 448)
    ⟨616, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_449 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨617, .push 2 961⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 449)
    ⟨617, .push 2 961⟩ (by rfl)

theorem entryDecoder_450 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨620, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 450)
    ⟨620, .op .JUMP⟩ (by rfl)

theorem entryDecoder_647 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨961, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 647)
    ⟨961, .op .JUMPDEST⟩ (by rfl)

theorem entryDecoder_648 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨962, .push 2 1006⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 648)
    ⟨962, .push 2 1006⟩ (by rfl)

theorem entryDecoder_649 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨965, .op .JUMP⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 649)
    ⟨965, .op .JUMP⟩ (by rfl)

theorem entryDecoder_682 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨1006, .op .JUMPDEST⟩ :=
  referenceCertifiedArtifact.decoderCertificate (rowIndex 682)
    ⟨1006, .op .JUMPDEST⟩ (by rfl)

abbrev EntrySite := Challenge.EvmProof.CertifiedArtifact.SelectedEntry
  .Osaka referenceBytecode

def entryPath_start : List EntrySite :=
  [
   ⟨⟨0, .push 2 27⟩, entryDecoder_0⟩,
   ⟨⟨3, .op .JUMP⟩, entryDecoder_1⟩
  ]

def entryPath_1b : List EntrySite :=
  [
   ⟨⟨27, .op .JUMPDEST⟩, entryDecoder_20⟩,
   ⟨⟨28, .push 2 46⟩, entryDecoder_21⟩,
   ⟨⟨31, .op .JUMP⟩, entryDecoder_22⟩
  ]

def entryPath_2e : List EntrySite :=
  [
   ⟨⟨46, .op .JUMPDEST⟩, entryDecoder_35⟩,
   ⟨⟨47, .push 2 70⟩, entryDecoder_36⟩,
   ⟨⟨50, .op .JUMP⟩, entryDecoder_37⟩
  ]

def entryPath_46 : List EntrySite :=
  [
   ⟨⟨70, .op .JUMPDEST⟩, entryDecoder_52⟩,
   ⟨⟨71, .push 2 90⟩, entryDecoder_53⟩,
   ⟨⟨74, .op .JUMP⟩, entryDecoder_54⟩
  ]

def entryPath_5a : List EntrySite :=
  [
   ⟨⟨90, .op .JUMPDEST⟩, entryDecoder_67⟩,
   ⟨⟨91, .push 2 115⟩, entryDecoder_68⟩,
   ⟨⟨94, .op .JUMP⟩, entryDecoder_69⟩
  ]

def entryPath_73 : List EntrySite :=
  [
   ⟨⟨115, .op .JUMPDEST⟩, entryDecoder_83⟩,
   ⟨⟨116, .push 2 142⟩, entryDecoder_84⟩,
   ⟨⟨119, .op .JUMP⟩, entryDecoder_85⟩
  ]

def entryPath_8e : List EntrySite :=
  [
   ⟨⟨142, .op .JUMPDEST⟩, entryDecoder_105⟩,
   ⟨⟨143, .push 2 271⟩, entryDecoder_106⟩,
   ⟨⟨146, .op .JUMP⟩, entryDecoder_107⟩
  ]

def entryPath_10f : List EntrySite :=
  [
   ⟨⟨271, .op .JUMPDEST⟩, entryDecoder_205⟩,
   ⟨⟨272, .push 2 434⟩, entryDecoder_206⟩,
   ⟨⟨275, .op .JUMP⟩, entryDecoder_207⟩
  ]

def entryPath_1b2 : List EntrySite :=
  [
   ⟨⟨434, .op .JUMPDEST⟩, entryDecoder_313⟩,
   ⟨⟨435, .push 2 475⟩, entryDecoder_314⟩,
   ⟨⟨438, .op .JUMP⟩, entryDecoder_315⟩
  ]

def entryPath_1db : List EntrySite :=
  [
   ⟨⟨475, .op .JUMPDEST⟩, entryDecoder_346⟩,
   ⟨⟨476, .push 2 561⟩, entryDecoder_347⟩,
   ⟨⟨479, .op .JUMP⟩, entryDecoder_348⟩
  ]

def entryPath_231 : List EntrySite :=
  [
   ⟨⟨561, .op .JUMPDEST⟩, entryDecoder_410⟩,
   ⟨⟨562, .push 2 616⟩, entryDecoder_411⟩,
   ⟨⟨565, .op .JUMP⟩, entryDecoder_412⟩
  ]

def entryPath_268 : List EntrySite :=
  [
   ⟨⟨616, .op .JUMPDEST⟩, entryDecoder_448⟩,
   ⟨⟨617, .push 2 961⟩, entryDecoder_449⟩,
   ⟨⟨620, .op .JUMP⟩, entryDecoder_450⟩
  ]

def entryPath_3c1 : List EntrySite :=
  [
   ⟨⟨961, .op .JUMPDEST⟩, entryDecoder_647⟩,
   ⟨⟨962, .push 2 1006⟩, entryDecoder_648⟩,
   ⟨⟨965, .op .JUMP⟩, entryDecoder_649⟩
  ]

def entryPath_3ee : List EntrySite :=
  [
   ⟨⟨1006, .op .JUMPDEST⟩, entryDecoder_682⟩
  ]

/-- The compact certified sites traversed between deployment entry and the
main RIPEMD body. Each bounded segment can be checked independently, while
the combined path remains definitionally their append chain. -/
def entrySelectedPath : List EntrySite :=
  entryPath_start ++ entryPath_1b ++ entryPath_2e ++ entryPath_46 ++
  entryPath_5a ++ entryPath_73 ++ entryPath_8e ++ entryPath_10f ++
  entryPath_1b2 ++ entryPath_1db ++ entryPath_231 ++ entryPath_268 ++
  entryPath_3c1 ++ entryPath_3ee


def referenceArtifact : Challenge.EvmProof.ProgramArtifact where
  code := referenceBytecode
  instructions := referenceInstructions
  assembly_eq := assemble_referenceInstructions

theorem certifiedArtifact_instructions :
    Challenge.EvmProof.CertifiedArtifact.instructions
        referenceCertifiedArtifact.rows = referenceInstructions := by
  rfl

def instructionPC (index : Nat) : Nat :=
  referenceArtifact.instructionPC index

/-- One of the straight-line stores which initializes RIPEMD's lookup tables,
round constants, and five-word initial chaining value. -/
structure InitStore where
  index : Nat
  valueWidth : Fin 33
  value : UInt256
  offsetWidth : Fin 33
  offset : UInt256

def initStores : List InitStore :=
  [⟨683, 31, 1780731860627700044960722568376592188711674974810043212252563479055960840, 2, 1184⟩,
   ⟨686, 32, 1374703749640218873849524064026661036561295975619335768036000015621818746370, 2, 1216⟩,
   ⟨689, 32, 1809286146446445343010337679715913357291520642540487409382712519614204477440, 2, 1248⟩,
   ⟨692, 32, 2286348414996307935469207465186628553155355030353023797310855598864584999170, 2, 1280⟩,
   ⟨695, 32, 6793533947442029545286681365244130742947859423983440781638017424580845963790, 2, 1312⟩,
   ⟨698, 32, 5454326014381509071620663843103927214778145566039445656282506490595801825280, 2, 1344⟩,
   ⟨701, 32, 5000281043567253289773844389228683908720941172611121566642559091978571025676, 2, 1376⟩,
   ⟨704, 32, 4998451946933852135137276647445154408072640462072745561656555001729660617996, 2, 1408⟩,
   ⟨707, 32, 4097353149147406276549177442451244923784709130172834976461593227075946283008, 2, 1440⟩,
   ⟨710, 32, 3634466825900925589093651101374881051901026410458987220032629834781140389131, 2, 1472⟩,
   ⟨713, 32, 4083287390302437702768465126624575726298108573653391417181074648310269415176, 2, 1504⟩,
   ⟨716, 32, 3627420088851531435467691758328083203359072412578514691593700216701345333248, 2, 1536⟩,
   ⟨719, 0, 0, 2, 1568⟩,
   ⟨722, 4, 1518500249, 2, 1600⟩,
   ⟨725, 4, 1859775393, 2, 1632⟩,
   ⟨728, 4, 2400959708, 2, 1664⟩,
   ⟨731, 4, 2840853838, 2, 1696⟩,
   ⟨734, 4, 1352829926, 2, 1728⟩,
   ⟨737, 4, 1548603684, 2, 1760⟩,
   ⟨740, 4, 1836072691, 2, 1792⟩,
   ⟨743, 4, 2053994217, 2, 1824⟩,
   ⟨746, 0, 0, 2, 1856⟩,
   ⟨749, 4, 1732584193, 1, 32⟩,
   ⟨752, 4, 4023233417, 1, 64⟩,
   ⟨755, 4, 2562383102, 1, 96⟩,
   ⟨758, 4, 271733878, 1, 128⟩,
   ⟨761, 4, 3285377520, 1, 160⟩]

theorem initStore_valid (w : InitStore) (hw : w ∈ initStores) :
    referenceInstructions[w.index]? = some (.push w.valueWidth w.value) ∧
    instructionPC (w.index + 1) = instructionPC w.index + w.valueWidth.val + 1 ∧
    referenceInstructions[w.index + 1]? = some (.push w.offsetWidth w.offset) ∧
    instructionPC (w.index + 2) = instructionPC (w.index + 1) + w.offsetWidth.val + 1 ∧
    referenceInstructions[w.index + 2]? = some (.op .MSTORE) ∧
    instructionPC (w.index + 3) = instructionPC (w.index + 2) + 1 := by
  simp only [initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals repeat' apply And.intro
  all_goals rfl

@[simp] theorem referenceArtifact_pc_683 :
    referenceArtifact.instructionPC 683 = 0x3ef := by rfl

@[simp] theorem referenceArtifact_pc_684 :
    referenceArtifact.instructionPC 684 = 0x40f := by rfl

@[simp] theorem referenceArtifact_pc_685 :
    referenceArtifact.instructionPC 685 = 0x412 := by rfl

@[simp] theorem referenceArtifact_pc_686 :
    referenceArtifact.instructionPC 686 = 0x413 := by rfl

@[simp] theorem referenceArtifact_pc_687 :
    referenceArtifact.instructionPC 687 = 0x434 := by rfl

@[simp] theorem referenceArtifact_pc_688 :
    referenceArtifact.instructionPC 688 = 0x437 := by rfl

@[simp] theorem referenceArtifact_pc_689 :
    referenceArtifact.instructionPC 689 = 0x438 := by rfl

@[simp] theorem referenceArtifact_pc_690 :
    referenceArtifact.instructionPC 690 = 0x459 := by rfl

@[simp] theorem referenceArtifact_pc_691 :
    referenceArtifact.instructionPC 691 = 0x45c := by rfl

@[simp] theorem referenceArtifact_pc_692 :
    referenceArtifact.instructionPC 692 = 0x45d := by rfl

@[simp] theorem referenceArtifact_pc_693 :
    referenceArtifact.instructionPC 693 = 0x47e := by rfl

@[simp] theorem referenceArtifact_pc_694 :
    referenceArtifact.instructionPC 694 = 0x481 := by rfl

@[simp] theorem referenceArtifact_pc_695 :
    referenceArtifact.instructionPC 695 = 0x482 := by rfl

@[simp] theorem referenceArtifact_pc_696 :
    referenceArtifact.instructionPC 696 = 0x4a3 := by rfl

@[simp] theorem referenceArtifact_pc_697 :
    referenceArtifact.instructionPC 697 = 0x4a6 := by rfl

@[simp] theorem referenceArtifact_pc_698 :
    referenceArtifact.instructionPC 698 = 0x4a7 := by rfl

@[simp] theorem referenceArtifact_pc_699 :
    referenceArtifact.instructionPC 699 = 0x4c8 := by rfl

@[simp] theorem referenceArtifact_pc_700 :
    referenceArtifact.instructionPC 700 = 0x4cb := by rfl

@[simp] theorem referenceArtifact_pc_701 :
    referenceArtifact.instructionPC 701 = 0x4cc := by rfl

@[simp] theorem referenceArtifact_pc_702 :
    referenceArtifact.instructionPC 702 = 0x4ed := by rfl

@[simp] theorem referenceArtifact_pc_703 :
    referenceArtifact.instructionPC 703 = 0x4f0 := by rfl

@[simp] theorem referenceArtifact_pc_704 :
    referenceArtifact.instructionPC 704 = 0x4f1 := by rfl

@[simp] theorem referenceArtifact_pc_705 :
    referenceArtifact.instructionPC 705 = 0x512 := by rfl

@[simp] theorem referenceArtifact_pc_706 :
    referenceArtifact.instructionPC 706 = 0x515 := by rfl

@[simp] theorem referenceArtifact_pc_707 :
    referenceArtifact.instructionPC 707 = 0x516 := by rfl

@[simp] theorem referenceArtifact_pc_708 :
    referenceArtifact.instructionPC 708 = 0x537 := by rfl

@[simp] theorem referenceArtifact_pc_709 :
    referenceArtifact.instructionPC 709 = 0x53a := by rfl

@[simp] theorem referenceArtifact_pc_710 :
    referenceArtifact.instructionPC 710 = 0x53b := by rfl

@[simp] theorem referenceArtifact_pc_711 :
    referenceArtifact.instructionPC 711 = 0x55c := by rfl

@[simp] theorem referenceArtifact_pc_712 :
    referenceArtifact.instructionPC 712 = 0x55f := by rfl

@[simp] theorem referenceArtifact_pc_713 :
    referenceArtifact.instructionPC 713 = 0x560 := by rfl

@[simp] theorem referenceArtifact_pc_714 :
    referenceArtifact.instructionPC 714 = 0x581 := by rfl

@[simp] theorem referenceArtifact_pc_715 :
    referenceArtifact.instructionPC 715 = 0x584 := by rfl

@[simp] theorem referenceArtifact_pc_716 :
    referenceArtifact.instructionPC 716 = 0x585 := by rfl

@[simp] theorem referenceArtifact_pc_717 :
    referenceArtifact.instructionPC 717 = 0x5a6 := by rfl

@[simp] theorem referenceArtifact_pc_718 :
    referenceArtifact.instructionPC 718 = 0x5a9 := by rfl

@[simp] theorem referenceArtifact_pc_719 :
    referenceArtifact.instructionPC 719 = 0x5aa := by rfl

@[simp] theorem referenceArtifact_pc_720 :
    referenceArtifact.instructionPC 720 = 0x5ab := by rfl

@[simp] theorem referenceArtifact_pc_721 :
    referenceArtifact.instructionPC 721 = 0x5ae := by rfl

@[simp] theorem referenceArtifact_pc_722 :
    referenceArtifact.instructionPC 722 = 0x5af := by rfl

@[simp] theorem referenceArtifact_pc_723 :
    referenceArtifact.instructionPC 723 = 0x5b4 := by rfl

@[simp] theorem referenceArtifact_pc_724 :
    referenceArtifact.instructionPC 724 = 0x5b7 := by rfl

@[simp] theorem referenceArtifact_pc_725 :
    referenceArtifact.instructionPC 725 = 0x5b8 := by rfl

@[simp] theorem referenceArtifact_pc_726 :
    referenceArtifact.instructionPC 726 = 0x5bd := by rfl

@[simp] theorem referenceArtifact_pc_727 :
    referenceArtifact.instructionPC 727 = 0x5c0 := by rfl

@[simp] theorem referenceArtifact_pc_728 :
    referenceArtifact.instructionPC 728 = 0x5c1 := by rfl

@[simp] theorem referenceArtifact_pc_729 :
    referenceArtifact.instructionPC 729 = 0x5c6 := by rfl

@[simp] theorem referenceArtifact_pc_730 :
    referenceArtifact.instructionPC 730 = 0x5c9 := by rfl

@[simp] theorem referenceArtifact_pc_731 :
    referenceArtifact.instructionPC 731 = 0x5ca := by rfl

@[simp] theorem referenceArtifact_pc_732 :
    referenceArtifact.instructionPC 732 = 0x5cf := by rfl

@[simp] theorem referenceArtifact_pc_733 :
    referenceArtifact.instructionPC 733 = 0x5d2 := by rfl

@[simp] theorem referenceArtifact_pc_734 :
    referenceArtifact.instructionPC 734 = 0x5d3 := by rfl

@[simp] theorem referenceArtifact_pc_735 :
    referenceArtifact.instructionPC 735 = 0x5d8 := by rfl

@[simp] theorem referenceArtifact_pc_736 :
    referenceArtifact.instructionPC 736 = 0x5db := by rfl

@[simp] theorem referenceArtifact_pc_737 :
    referenceArtifact.instructionPC 737 = 0x5dc := by rfl

@[simp] theorem referenceArtifact_pc_738 :
    referenceArtifact.instructionPC 738 = 0x5e1 := by rfl

@[simp] theorem referenceArtifact_pc_739 :
    referenceArtifact.instructionPC 739 = 0x5e4 := by rfl

@[simp] theorem referenceArtifact_pc_740 :
    referenceArtifact.instructionPC 740 = 0x5e5 := by rfl

@[simp] theorem referenceArtifact_pc_741 :
    referenceArtifact.instructionPC 741 = 0x5ea := by rfl

@[simp] theorem referenceArtifact_pc_742 :
    referenceArtifact.instructionPC 742 = 0x5ed := by rfl

@[simp] theorem referenceArtifact_pc_743 :
    referenceArtifact.instructionPC 743 = 0x5ee := by rfl

@[simp] theorem referenceArtifact_pc_744 :
    referenceArtifact.instructionPC 744 = 0x5f3 := by rfl

@[simp] theorem referenceArtifact_pc_745 :
    referenceArtifact.instructionPC 745 = 0x5f6 := by rfl

@[simp] theorem referenceArtifact_pc_746 :
    referenceArtifact.instructionPC 746 = 0x5f7 := by rfl

@[simp] theorem referenceArtifact_pc_747 :
    referenceArtifact.instructionPC 747 = 0x5f8 := by rfl

@[simp] theorem referenceArtifact_pc_748 :
    referenceArtifact.instructionPC 748 = 0x5fb := by rfl

@[simp] theorem referenceArtifact_pc_749 :
    referenceArtifact.instructionPC 749 = 0x5fc := by rfl

@[simp] theorem referenceArtifact_pc_750 :
    referenceArtifact.instructionPC 750 = 0x601 := by rfl

@[simp] theorem referenceArtifact_pc_751 :
    referenceArtifact.instructionPC 751 = 0x603 := by rfl

@[simp] theorem referenceArtifact_pc_752 :
    referenceArtifact.instructionPC 752 = 0x604 := by rfl

@[simp] theorem referenceArtifact_pc_753 :
    referenceArtifact.instructionPC 753 = 0x609 := by rfl

@[simp] theorem referenceArtifact_pc_754 :
    referenceArtifact.instructionPC 754 = 0x60b := by rfl

@[simp] theorem referenceArtifact_pc_755 :
    referenceArtifact.instructionPC 755 = 0x60c := by rfl

@[simp] theorem referenceArtifact_pc_756 :
    referenceArtifact.instructionPC 756 = 0x611 := by rfl

@[simp] theorem referenceArtifact_pc_757 :
    referenceArtifact.instructionPC 757 = 0x613 := by rfl

@[simp] theorem referenceArtifact_pc_758 :
    referenceArtifact.instructionPC 758 = 0x614 := by rfl

@[simp] theorem referenceArtifact_pc_759 :
    referenceArtifact.instructionPC 759 = 0x619 := by rfl

@[simp] theorem referenceArtifact_pc_760 :
    referenceArtifact.instructionPC 760 = 0x61b := by rfl

@[simp] theorem referenceArtifact_pc_761 :
    referenceArtifact.instructionPC 761 = 0x61c := by rfl

@[simp] theorem referenceArtifact_pc_762 :
    referenceArtifact.instructionPC 762 = 0x621 := by rfl

@[simp] theorem referenceArtifact_pc_763 :
    referenceArtifact.instructionPC 763 = 0x623 := by rfl


@[simp] theorem referenceArtifact_pc_764 :
    referenceArtifact.instructionPC 764 = 0x624 := by rfl

@[simp] theorem referenceArtifact_pc_765 :
    referenceArtifact.instructionPC 765 = 0x627 := by rfl

@[simp] theorem referenceArtifact_pc_766 :
    referenceArtifact.instructionPC 766 = 0x628 := by rfl

@[simp] theorem referenceArtifact_pc_767 :
    referenceArtifact.instructionPC 767 = 0x62b := by rfl

@[simp] theorem referenceArtifact_pc_0 :
    referenceArtifact.instructionPC 0 = 0x0 := by rfl

@[simp] theorem referenceArtifact_pc_1 :
    referenceArtifact.instructionPC 1 = 0x3 := by rfl

@[simp] theorem referenceArtifact_pc_20 :
    referenceArtifact.instructionPC 20 = 0x1b := by rfl

@[simp] theorem referenceArtifact_pc_21 :
    referenceArtifact.instructionPC 21 = 0x1c := by rfl

@[simp] theorem referenceArtifact_pc_22 :
    referenceArtifact.instructionPC 22 = 0x1f := by rfl

@[simp] theorem referenceArtifact_pc_35 :
    referenceArtifact.instructionPC 35 = 0x2e := by rfl

@[simp] theorem referenceArtifact_pc_36 :
    referenceArtifact.instructionPC 36 = 0x2f := by rfl

@[simp] theorem referenceArtifact_pc_37 :
    referenceArtifact.instructionPC 37 = 0x32 := by rfl

@[simp] theorem referenceArtifact_pc_52 :
    referenceArtifact.instructionPC 52 = 0x46 := by rfl

@[simp] theorem referenceArtifact_pc_53 :
    referenceArtifact.instructionPC 53 = 0x47 := by rfl

@[simp] theorem referenceArtifact_pc_54 :
    referenceArtifact.instructionPC 54 = 0x4a := by rfl

@[simp] theorem referenceArtifact_pc_67 :
    referenceArtifact.instructionPC 67 = 0x5a := by rfl

@[simp] theorem referenceArtifact_pc_68 :
    referenceArtifact.instructionPC 68 = 0x5b := by rfl

@[simp] theorem referenceArtifact_pc_69 :
    referenceArtifact.instructionPC 69 = 0x5e := by rfl

@[simp] theorem referenceArtifact_pc_83 :
    referenceArtifact.instructionPC 83 = 0x73 := by rfl

@[simp] theorem referenceArtifact_pc_84 :
    referenceArtifact.instructionPC 84 = 0x74 := by rfl

@[simp] theorem referenceArtifact_pc_85 :
    referenceArtifact.instructionPC 85 = 0x77 := by rfl

@[simp] theorem referenceArtifact_pc_105 :
    referenceArtifact.instructionPC 105 = 0x8e := by rfl

@[simp] theorem referenceArtifact_pc_106 :
    referenceArtifact.instructionPC 106 = 0x8f := by rfl

@[simp] theorem referenceArtifact_pc_107 :
    referenceArtifact.instructionPC 107 = 0x92 := by rfl

@[simp] theorem referenceArtifact_pc_205 :
    referenceArtifact.instructionPC 205 = 0x10f := by rfl

@[simp] theorem referenceArtifact_pc_206 :
    referenceArtifact.instructionPC 206 = 0x110 := by rfl

@[simp] theorem referenceArtifact_pc_207 :
    referenceArtifact.instructionPC 207 = 0x113 := by rfl

@[simp] theorem referenceArtifact_pc_313 :
    referenceArtifact.instructionPC 313 = 0x1b2 := by rfl

@[simp] theorem referenceArtifact_pc_314 :
    referenceArtifact.instructionPC 314 = 0x1b3 := by rfl

@[simp] theorem referenceArtifact_pc_315 :
    referenceArtifact.instructionPC 315 = 0x1b6 := by rfl

@[simp] theorem referenceArtifact_pc_346 :
    referenceArtifact.instructionPC 346 = 0x1db := by rfl

@[simp] theorem referenceArtifact_pc_347 :
    referenceArtifact.instructionPC 347 = 0x1dc := by rfl

@[simp] theorem referenceArtifact_pc_348 :
    referenceArtifact.instructionPC 348 = 0x1df := by rfl

@[simp] theorem referenceArtifact_pc_410 :
    referenceArtifact.instructionPC 410 = 0x231 := by rfl

@[simp] theorem referenceArtifact_pc_411 :
    referenceArtifact.instructionPC 411 = 0x232 := by rfl

@[simp] theorem referenceArtifact_pc_412 :
    referenceArtifact.instructionPC 412 = 0x235 := by rfl

@[simp] theorem referenceArtifact_pc_448 :
    referenceArtifact.instructionPC 448 = 0x268 := by rfl

@[simp] theorem referenceArtifact_pc_449 :
    referenceArtifact.instructionPC 449 = 0x269 := by rfl

@[simp] theorem referenceArtifact_pc_450 :
    referenceArtifact.instructionPC 450 = 0x26c := by rfl

@[simp] theorem referenceArtifact_pc_647 :
    referenceArtifact.instructionPC 647 = 0x3c1 := by rfl

@[simp] theorem referenceArtifact_pc_648 :
    referenceArtifact.instructionPC 648 = 0x3c2 := by rfl

@[simp] theorem referenceArtifact_pc_649 :
    referenceArtifact.instructionPC 649 = 0x3c5 := by rfl

@[simp] theorem referenceArtifact_pc_682 :
    referenceArtifact.instructionPC 682 = 0x3ee := by rfl

@[simp] theorem validJumpDest_1b :
    Decode.isValidJumpDest referenceBytecode 0x1b = true := by
  have h := referenceArtifact.isValidJumpDest_index 20 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 20) = true at h
  simpa using h

@[simp] theorem validJumpDest_2e :
    Decode.isValidJumpDest referenceBytecode 0x2e = true := by
  have h := referenceArtifact.isValidJumpDest_index 35 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 35) = true at h
  simpa using h

@[simp] theorem validJumpDest_46 :
    Decode.isValidJumpDest referenceBytecode 0x46 = true := by
  have h := referenceArtifact.isValidJumpDest_index 52 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 52) = true at h
  simpa using h

@[simp] theorem validJumpDest_5a :
    Decode.isValidJumpDest referenceBytecode 0x5a = true := by
  have h := referenceArtifact.isValidJumpDest_index 67 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 67) = true at h
  simpa using h

@[simp] theorem validJumpDest_73 :
    Decode.isValidJumpDest referenceBytecode 0x73 = true := by
  have h := referenceArtifact.isValidJumpDest_index 83 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 83) = true at h
  simpa using h

@[simp] theorem validJumpDest_8e :
    Decode.isValidJumpDest referenceBytecode 0x8e = true := by
  have h := referenceArtifact.isValidJumpDest_index 105 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 105) = true at h
  simpa using h

@[simp] theorem validJumpDest_10f :
    Decode.isValidJumpDest referenceBytecode 0x10f = true := by
  have h := referenceArtifact.isValidJumpDest_index 205 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 205) = true at h
  simpa using h

@[simp] theorem validJumpDest_1b2 :
    Decode.isValidJumpDest referenceBytecode 0x1b2 = true := by
  have h := referenceArtifact.isValidJumpDest_index 313 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 313) = true at h
  simpa using h

@[simp] theorem validJumpDest_1db :
    Decode.isValidJumpDest referenceBytecode 0x1db = true := by
  have h := referenceArtifact.isValidJumpDest_index 346 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 346) = true at h
  simpa using h

@[simp] theorem validJumpDest_231 :
    Decode.isValidJumpDest referenceBytecode 0x231 = true := by
  have h := referenceArtifact.isValidJumpDest_index 410 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 410) = true at h
  simpa using h

@[simp] theorem validJumpDest_268 :
    Decode.isValidJumpDest referenceBytecode 0x268 = true := by
  have h := referenceArtifact.isValidJumpDest_index 448 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 448) = true at h
  simpa using h

@[simp] theorem validJumpDest_3c1 :
    Decode.isValidJumpDest referenceBytecode 0x3c1 = true := by
  have h := referenceArtifact.isValidJumpDest_index 647 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 647) = true at h
  simpa using h

@[simp] theorem validJumpDest_3ee :
    Decode.isValidJumpDest referenceBytecode 0x3ee = true := by
  have h := referenceArtifact.isValidJumpDest_index 682 (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 682) = true at h
  simpa using h

@[simp] theorem refPc349 :
    referenceArtifact.instructionPC 349 = 0x1e0 := by rfl
@[simp] theorem pc349 :
    instructionPC 349 = 0x1e0 := by rfl

@[simp] theorem refPc350 :
    referenceArtifact.instructionPC 350 = 0x1e1 := by rfl
@[simp] theorem pc350 :
    instructionPC 350 = 0x1e1 := by rfl

@[simp] theorem refPc351 :
    referenceArtifact.instructionPC 351 = 0x1e2 := by rfl
@[simp] theorem pc351 :
    instructionPC 351 = 0x1e2 := by rfl

@[simp] theorem refPc352 :
    referenceArtifact.instructionPC 352 = 0x1e4 := by rfl
@[simp] theorem pc352 :
    instructionPC 352 = 0x1e4 := by rfl

@[simp] theorem refPc353 :
    referenceArtifact.instructionPC 353 = 0x1e5 := by rfl
@[simp] theorem pc353 :
    instructionPC 353 = 0x1e5 := by rfl

@[simp] theorem refPc354 :
    referenceArtifact.instructionPC 354 = 0x1e6 := by rfl
@[simp] theorem pc354 :
    instructionPC 354 = 0x1e6 := by rfl

@[simp] theorem refPc355 :
    referenceArtifact.instructionPC 355 = 0x1e8 := by rfl
@[simp] theorem pc355 :
    instructionPC 355 = 0x1e8 := by rfl

@[simp] theorem refPc356 :
    referenceArtifact.instructionPC 356 = 0x1e9 := by rfl
@[simp] theorem pc356 :
    instructionPC 356 = 0x1e9 := by rfl

@[simp] theorem refPc357 :
    referenceArtifact.instructionPC 357 = 0x1eb := by rfl
@[simp] theorem pc357 :
    instructionPC 357 = 0x1eb := by rfl

@[simp] theorem refPc358 :
    referenceArtifact.instructionPC 358 = 0x1ec := by rfl
@[simp] theorem pc358 :
    instructionPC 358 = 0x1ec := by rfl

@[simp] theorem refPc359 :
    referenceArtifact.instructionPC 359 = 0x1ed := by rfl
@[simp] theorem pc359 :
    instructionPC 359 = 0x1ed := by rfl

@[simp] theorem refPc360 :
    referenceArtifact.instructionPC 360 = 0x1ee := by rfl
@[simp] theorem pc360 :
    instructionPC 360 = 0x1ee := by rfl

@[simp] theorem refPc361 :
    referenceArtifact.instructionPC 361 = 0x1ef := by rfl
@[simp] theorem pc361 :
    instructionPC 361 = 0x1ef := by rfl

@[simp] theorem refPc362 :
    referenceArtifact.instructionPC 362 = 0x1f0 := by rfl
@[simp] theorem pc362 :
    instructionPC 362 = 0x1f0 := by rfl

@[simp] theorem refPc363 :
    referenceArtifact.instructionPC 363 = 0x1f3 := by rfl
@[simp] theorem pc363 :
    instructionPC 363 = 0x1f3 := by rfl

@[simp] theorem refPc364 :
    referenceArtifact.instructionPC 364 = 0x1f4 := by rfl
@[simp] theorem pc364 :
    instructionPC 364 = 0x1f4 := by rfl

@[simp] theorem refPc365 :
    referenceArtifact.instructionPC 365 = 0x1f6 := by rfl
@[simp] theorem pc365 :
    instructionPC 365 = 0x1f6 := by rfl

@[simp] theorem refPc366 :
    referenceArtifact.instructionPC 366 = 0x1f7 := by rfl
@[simp] theorem pc366 :
    instructionPC 366 = 0x1f7 := by rfl

@[simp] theorem refPc367 :
    referenceArtifact.instructionPC 367 = 0x1fa := by rfl
@[simp] theorem pc367 :
    instructionPC 367 = 0x1fa := by rfl

@[simp] theorem refPc368 :
    referenceArtifact.instructionPC 368 = 0x1fb := by rfl
@[simp] theorem pc368 :
    instructionPC 368 = 0x1fb := by rfl

@[simp] theorem refPc369 :
    referenceArtifact.instructionPC 369 = 0x1fc := by rfl
@[simp] theorem pc369 :
    instructionPC 369 = 0x1fc := by rfl

@[simp] theorem refPc370 :
    referenceArtifact.instructionPC 370 = 0x1fd := by rfl
@[simp] theorem pc370 :
    instructionPC 370 = 0x1fd := by rfl

@[simp] theorem refPc371 :
    referenceArtifact.instructionPC 371 = 0x1ff := by rfl
@[simp] theorem pc371 :
    instructionPC 371 = 0x1ff := by rfl

@[simp] theorem refPc372 :
    referenceArtifact.instructionPC 372 = 0x200 := by rfl
@[simp] theorem pc372 :
    instructionPC 372 = 0x200 := by rfl

@[simp] theorem refPc373 :
    referenceArtifact.instructionPC 373 = 0x202 := by rfl
@[simp] theorem pc373 :
    instructionPC 373 = 0x202 := by rfl

@[simp] theorem refPc374 :
    referenceArtifact.instructionPC 374 = 0x203 := by rfl
@[simp] theorem pc374 :
    instructionPC 374 = 0x203 := by rfl

@[simp] theorem refPc375 :
    referenceArtifact.instructionPC 375 = 0x204 := by rfl
@[simp] theorem pc375 :
    instructionPC 375 = 0x204 := by rfl

@[simp] theorem refPc376 :
    referenceArtifact.instructionPC 376 = 0x207 := by rfl
@[simp] theorem pc376 :
    instructionPC 376 = 0x207 := by rfl

@[simp] theorem refPc377 :
    referenceArtifact.instructionPC 377 = 0x208 := by rfl
@[simp] theorem pc377 :
    instructionPC 377 = 0x208 := by rfl

@[simp] theorem refPc378 :
    referenceArtifact.instructionPC 378 = 0x209 := by rfl
@[simp] theorem pc378 :
    instructionPC 378 = 0x209 := by rfl

@[simp] theorem refPc379 :
    referenceArtifact.instructionPC 379 = 0x20a := by rfl
@[simp] theorem pc379 :
    instructionPC 379 = 0x20a := by rfl

@[simp] theorem refPc380 :
    referenceArtifact.instructionPC 380 = 0x20c := by rfl
@[simp] theorem pc380 :
    instructionPC 380 = 0x20c := by rfl

@[simp] theorem refPc381 :
    referenceArtifact.instructionPC 381 = 0x20d := by rfl
@[simp] theorem pc381 :
    instructionPC 381 = 0x20d := by rfl

@[simp] theorem refPc382 :
    referenceArtifact.instructionPC 382 = 0x20e := by rfl
@[simp] theorem pc382 :
    instructionPC 382 = 0x20e := by rfl

@[simp] theorem refPc383 :
    referenceArtifact.instructionPC 383 = 0x20f := by rfl
@[simp] theorem pc383 :
    instructionPC 383 = 0x20f := by rfl

@[simp] theorem refPc384 :
    referenceArtifact.instructionPC 384 = 0x212 := by rfl
@[simp] theorem pc384 :
    instructionPC 384 = 0x212 := by rfl

@[simp] theorem refPc385 :
    referenceArtifact.instructionPC 385 = 0x213 := by rfl
@[simp] theorem pc385 :
    instructionPC 385 = 0x213 := by rfl

@[simp] theorem refPc386 :
    referenceArtifact.instructionPC 386 = 0x215 := by rfl
@[simp] theorem pc386 :
    instructionPC 386 = 0x215 := by rfl

@[simp] theorem refPc387 :
    referenceArtifact.instructionPC 387 = 0x216 := by rfl
@[simp] theorem pc387 :
    instructionPC 387 = 0x216 := by rfl

@[simp] theorem refPc388 :
    referenceArtifact.instructionPC 388 = 0x217 := by rfl
@[simp] theorem pc388 :
    instructionPC 388 = 0x217 := by rfl

@[simp] theorem refPc389 :
    referenceArtifact.instructionPC 389 = 0x219 := by rfl
@[simp] theorem pc389 :
    instructionPC 389 = 0x219 := by rfl

@[simp] theorem refPc390 :
    referenceArtifact.instructionPC 390 = 0x21a := by rfl
@[simp] theorem pc390 :
    instructionPC 390 = 0x21a := by rfl

@[simp] theorem refPc391 :
    referenceArtifact.instructionPC 391 = 0x21b := by rfl
@[simp] theorem pc391 :
    instructionPC 391 = 0x21b := by rfl

@[simp] theorem refPc392 :
    referenceArtifact.instructionPC 392 = 0x21c := by rfl
@[simp] theorem pc392 :
    instructionPC 392 = 0x21c := by rfl

@[simp] theorem refPc393 :
    referenceArtifact.instructionPC 393 = 0x21d := by rfl
@[simp] theorem pc393 :
    instructionPC 393 = 0x21d := by rfl

@[simp] theorem refPc394 :
    referenceArtifact.instructionPC 394 = 0x21e := by rfl
@[simp] theorem pc394 :
    instructionPC 394 = 0x21e := by rfl

@[simp] theorem refPc395 :
    referenceArtifact.instructionPC 395 = 0x21f := by rfl
@[simp] theorem pc395 :
    instructionPC 395 = 0x21f := by rfl

@[simp] theorem refPc396 :
    referenceArtifact.instructionPC 396 = 0x220 := by rfl
@[simp] theorem pc396 :
    instructionPC 396 = 0x220 := by rfl

@[simp] theorem refPc397 :
    referenceArtifact.instructionPC 397 = 0x222 := by rfl
@[simp] theorem pc397 :
    instructionPC 397 = 0x222 := by rfl

@[simp] theorem refPc398 :
    referenceArtifact.instructionPC 398 = 0x223 := by rfl
@[simp] theorem pc398 :
    instructionPC 398 = 0x223 := by rfl

@[simp] theorem refPc399 :
    referenceArtifact.instructionPC 399 = 0x224 := by rfl
@[simp] theorem pc399 :
    instructionPC 399 = 0x224 := by rfl

@[simp] theorem refPc400 :
    referenceArtifact.instructionPC 400 = 0x225 := by rfl
@[simp] theorem pc400 :
    instructionPC 400 = 0x225 := by rfl

@[simp] theorem refPc401 :
    referenceArtifact.instructionPC 401 = 0x226 := by rfl
@[simp] theorem pc401 :
    instructionPC 401 = 0x226 := by rfl

@[simp] theorem refPc402 :
    referenceArtifact.instructionPC 402 = 0x229 := by rfl
@[simp] theorem pc402 :
    instructionPC 402 = 0x229 := by rfl

@[simp] theorem refPc403 :
    referenceArtifact.instructionPC 403 = 0x22a := by rfl
@[simp] theorem pc403 :
    instructionPC 403 = 0x22a := by rfl

@[simp] theorem refPc404 :
    referenceArtifact.instructionPC 404 = 0x22b := by rfl
@[simp] theorem pc404 :
    instructionPC 404 = 0x22b := by rfl

@[simp] theorem refPc405 :
    referenceArtifact.instructionPC 405 = 0x22c := by rfl
@[simp] theorem pc405 :
    instructionPC 405 = 0x22c := by rfl

@[simp] theorem refPc406 :
    referenceArtifact.instructionPC 406 = 0x22d := by rfl
@[simp] theorem pc406 :
    instructionPC 406 = 0x22d := by rfl

@[simp] theorem refPc407 :
    referenceArtifact.instructionPC 407 = 0x22e := by rfl
@[simp] theorem pc407 :
    instructionPC 407 = 0x22e := by rfl

@[simp] theorem refPc408 :
    referenceArtifact.instructionPC 408 = 0x22f := by rfl
@[simp] theorem pc408 :
    instructionPC 408 = 0x22f := by rfl

@[simp] theorem refPc409 :
    referenceArtifact.instructionPC 409 = 0x230 := by rfl
@[simp] theorem pc409 :
    instructionPC 409 = 0x230 := by rfl

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- Cached located path for the main-body call into `pad`. -/
def padEnterPath : List
    (Challenge.EvmProof.Stepper.Located referenceArtifact .Osaka) :=
  [⟨764, .push ⟨2, by decide⟩ (UInt256.ofNat 0x62c), by rfl, by decide⟩,
   ⟨765, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨766, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1e0), by rfl, by decide⟩,
   ⟨767, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for RIPEMD padded-length arithmetic. -/
def padLengthPath : List
    (Challenge.EvmProof.Stepper.Located referenceArtifact .Osaka) :=
  [⟨349, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨350, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨351, .push ⟨1, by decide⟩ (UInt256.ofNat 72), by rfl, by decide⟩,
   ⟨352, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨353, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨354, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨355, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨356, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨357, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨358, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨359, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for copying calldata and setting up the footer loop. -/
def padSetupPath : List
    (Challenge.EvmProof.Stepper.Located referenceArtifact .Osaka) :=
  [⟨360, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨361, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨362, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by rfl, by decide⟩,
   ⟨363, .op .CALLDATACOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨364, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨365, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨366, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by rfl, by decide⟩,
   ⟨367, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨368, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨369, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨370, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨371, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨372, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨373, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨374, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨375, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by rfl, by decide⟩,
   ⟨376, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨377, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨378, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]


end Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
