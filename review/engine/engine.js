/*!
 * Blizzard — шахматный движок, версия 0.1
 *
 * Всё в одном файле, без зависимостей:
 *   • правила шахмат (доска 0x88, генерация ходов, FEN, SAN, UCI-нотация);
 *   • оценка позиции (таблицы PeSTO + пешечная структура, мобильность,
 *     безопасность короля, проходные пешки, эндшпильные поправки);
 *   • поиск (итеративное углубление, PVS альфа-бета, таблица транспозиций,
 *     null move, LMR, futility/LMP, quiescence + SEE, killer/history/countermove,
 *     аспирационные окна, MultiPV);
 *   • уровни сложности и модель вероятностей исхода (выигрыш/ничья/проигрыш).
 *
 * Работает в браузере (Web Worker или основной поток) и в Node.js (см. uci.js).
 */
(function (global) {
'use strict';

const VERSION = '1.0';
const NAME = 'Blizzard';

// ------------------------------------------------------------------ константы
const WHITE = 0, BLACK = 1;
const PAWN = 1, KNIGHT = 2, BISHOP = 3, ROOK = 4, QUEEN = 5, KING = 6;
const F_NONE = 0, F_DOUBLE = 1, F_EP = 2, F_CASTLE = 3;
const MATE = 32000, MATE_BOUND = 31000, INF = 32500, MAX_PLY = 120;
// Оценки сети в сантипешках чуть крупнее, чем у Stockfish: на 1411 позициях медиана отношения SF/Blizzard — 0,92
// (tools/eval-calib.js, Stockfish 16 на миллион узлов). Показываемые оценки ядра умножаются на это число.
const CP_SCALE = 0.92;
const TT_EXACT = 1, TT_LOWER = 2, TT_UPPER = 3;
const START_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1';

const KNIGHT_OFF = [33, 31, 18, 14, -14, -18, -31, -33];
const KING_OFF = [1, -1, 16, -16, 15, 17, -15, -17];
const DIAG = [15, 17, -15, -17];
const ORTHO = [1, -1, 16, -16];
// LINE[a − b + 119] = 1, если поля a и b на одной линии (горизонталь, вертикаль, диагональ)
const LINE = new Uint8Array(240);
// ATT_MASK[поле − откуда + 119]: 1 — так бьёт конь, 2 — король, 4 — по диагонали, 8 — по линии; ATT_DIR — шаг луча
const ATT_MASK = new Uint8Array(240), ATT_DIR = new Int8Array(240);
for (const d of [33, 31, 18, 14, -14, -18, -31, -33]) ATT_MASK[d + 119] |= 1;
for (const d of [1, -1, 16, -16, 15, 17, -15, -17]) ATT_MASK[d + 119] |= 2;
for (const d of [15, 17, -15, -17]) for (let k = 1; k < 8; k++) { ATT_MASK[k * d + 119] |= 4; ATT_DIR[k * d + 119] = d; }
for (const d of [1, -1, 16, -16]) for (let k = 1; k < 8; k++) { ATT_MASK[k * d + 119] |= 8; ATT_DIR[k * d + 119] = d; }
for (const d of [15, 17, -15, -17, 1, -1, 16, -16]) for (let k = 1; k < 8; k++) LINE[k * d + 119] = 1;

const PIECE_CHARS = ' PNBRQK  pnbrqk ';
const PIECE_FROM_CHAR = { P: 1, N: 2, B: 3, R: 4, Q: 5, K: 6, p: 9, n: 10, b: 11, r: 12, q: 13, k: 14 };

const now = (typeof performance !== 'undefined' && performance.now)
  ? () => performance.now() : () => Date.now();

function mkMove(from, to, promo, flag, cap) {
  return from | (to << 7) | (promo << 14) | (flag << 17) | (cap << 20);
}
function sqName(s) { return 'abcdefgh'[s & 7] + ((s >> 4) + 1); }
function parseSq(str) {
  if (!str || str.length < 2) return -1;
  const f = str.charCodeAt(0) - 97, r = str.charCodeAt(1) - 49;
  if (f < 0 || f > 7 || r < 0 || r > 7) return -1;
  return r * 16 + f;
}
function sqDist(a, b) {
  return Math.max(Math.abs((a & 7) - (b & 7)), Math.abs((a >> 4) - (b >> 4)));
}

// ------------------------------------------------------------------ Zobrist
let rngState = 0x2545F491;
function rnd32() {
  rngState ^= rngState << 13; rngState ^= rngState >>> 17; rngState ^= rngState << 5;
  return rngState | 0;
}
const Z_PIECE_LO = new Int32Array(16 * 128), Z_PIECE_HI = new Int32Array(16 * 128);
for (let i = 0; i < 16 * 128; i++) { Z_PIECE_LO[i] = rnd32(); Z_PIECE_HI[i] = rnd32(); }
const Z_SIDE_LO = rnd32(), Z_SIDE_HI = rnd32();
const Z_CASTLE_LO = new Int32Array(16), Z_CASTLE_HI = new Int32Array(16);
for (let i = 0; i < 16; i++) { Z_CASTLE_LO[i] = rnd32(); Z_CASTLE_HI[i] = rnd32(); }
const Z_EP_LO = new Int32Array(8), Z_EP_HI = new Int32Array(8);
for (let i = 0; i < 8; i++) { Z_EP_LO[i] = rnd32(); Z_EP_HI[i] = rnd32(); }

// права на рокировку: 1 = K, 2 = Q, 4 = k, 8 = q
const CASTLE_MASK = new Int8Array(128).fill(15);
CASTLE_MASK[0] = 15 & ~2; CASTLE_MASK[7] = 15 & ~1; CASTLE_MASK[4] = 15 & ~3;
CASTLE_MASK[112] = 15 & ~8; CASTLE_MASK[119] = 15 & ~4; CASTLE_MASK[116] = 15 & ~12;

// ------------------------------------------------------------------ PeSTO
// Таблицы записаны с поля a8 (как в оригинале), для белых индекс = sq64 ^ 56.
const MG_VAL = [0, 82, 337, 365, 477, 1025, 0];
const EG_VAL = [0, 94, 281, 297, 512, 936, 0];
const PHASE_INC = [0, 0, 1, 1, 2, 4, 0, 0];
const PST_MG = [null,
  [0, 0, 0, 0, 0, 0, 0, 0, 98, 134, 61, 95, 68, 126, 34, -11, -6, 7, 26, 31, 65, 56, 25, -20, -14, 13, 6, 21, 23, 12, 17, -23, -27, -2, -5, 12, 17, 6, 10, -25, -26, -4, -4, -10, 3, 3, 33, -12, -35, -1, -20, -23, -15, 24, 38, -22, 0, 0, 0, 0, 0, 0, 0, 0],
  [-167, -89, -34, -49, 61, -97, -15, -107, -73, -41, 72, 36, 23, 62, 7, -17, -47, 60, 37, 65, 84, 129, 73, 44, -9, 17, 19, 53, 37, 69, 18, 22, -13, 4, 16, 13, 28, 19, 21, -8, -23, -9, 12, 10, 19, 17, 25, -16, -29, -53, -12, -3, -1, 18, -14, -19, -105, -21, -58, -33, -17, -28, -19, -23],
  [-29, 4, -82, -37, -25, -42, 7, -8, -26, 16, -18, -13, 30, 59, 18, -47, -16, 37, 43, 40, 35, 50, 37, -2, -4, 5, 19, 50, 37, 37, 7, -2, -6, 13, 13, 26, 34, 12, 10, 4, 0, 15, 15, 15, 14, 27, 18, 10, 4, 15, 16, 0, 7, 21, 33, 1, -33, -3, -14, -21, -13, -12, -39, -21],
  [32, 42, 32, 51, 63, 9, 31, 43, 27, 32, 58, 62, 80, 67, 26, 44, -5, 19, 26, 36, 17, 45, 61, 16, -24, -11, 7, 26, 24, 35, -8, -20, -36, -26, -12, -1, 9, -7, 6, -23, -45, -25, -16, -17, 3, 0, -5, -33, -44, -16, -20, -9, -1, 11, -6, -71, -19, -13, 1, 17, 16, 7, -37, -26],
  [-28, 0, 29, 12, 59, 44, 43, 45, -24, -39, -5, 1, -16, 57, 28, 54, -13, -17, 7, 8, 29, 56, 47, 57, -27, -27, -16, -16, -1, 17, -2, 1, -9, -26, -9, -10, -2, -4, 3, -3, -14, 2, -11, -2, -5, 2, 14, 5, -35, -8, 11, 2, 8, 15, -3, 1, -1, -18, -9, 10, -15, -25, -31, -50],
  [-65, 23, 16, -15, -56, -34, 2, 13, 29, -1, -20, -7, -8, -4, -38, -29, -9, 24, 2, -16, -20, 6, 22, -22, -17, -20, -12, -27, -30, -25, -14, -36, -49, -1, -27, -39, -46, -44, -33, -51, -14, -14, -22, -46, -44, -30, -15, -27, 1, 7, -8, -64, -43, -16, 9, 8, -15, 36, 12, -54, 8, -28, 24, 14],
];
const PST_EG = [null,
  [0, 0, 0, 0, 0, 0, 0, 0, 178, 173, 158, 134, 147, 132, 165, 187, 94, 100, 85, 67, 56, 53, 82, 84, 32, 24, 13, 5, -2, 4, 17, 17, 13, 9, -3, -7, -7, -8, 3, -1, 4, 7, -6, 1, 0, -5, -1, -8, 13, 8, 8, 10, 13, 0, 2, -7, 0, 0, 0, 0, 0, 0, 0, 0],
  [-58, -38, -13, -28, -31, -27, -63, -99, -25, -8, -25, -2, -9, -25, -24, -52, -24, -20, 10, 9, -1, -9, -19, -41, -17, 3, 22, 22, 22, 11, 8, -18, -18, -6, 16, 25, 16, 17, 4, -18, -23, -3, -1, 15, 10, -3, -20, -22, -42, -20, -10, -5, -2, -20, -23, -44, -29, -51, -23, -15, -22, -18, -50, -64],
  [-14, -21, -11, -8, -7, -9, -17, -24, -8, -4, 7, -12, -3, -13, -4, -14, 2, -8, 0, -1, -2, 6, 0, 4, -3, 9, 12, 9, 14, 10, 3, 2, -6, 3, 13, 19, 7, 10, -3, -9, -12, -3, 8, 10, 13, 3, -7, -15, -14, -18, -7, -1, 4, -9, -15, -27, -23, -9, -23, -5, -9, -16, -5, -17],
  [13, 10, 18, 15, 12, 12, 8, 5, 11, 13, 13, 11, -3, 3, 8, 3, 7, 7, 7, 5, 4, -3, -5, -3, 4, 3, 13, 1, 2, 1, -1, 2, 3, 5, 8, 4, -5, -6, -8, -11, -4, 0, -5, -1, -7, -12, -8, -16, -6, -6, 0, 2, -9, -9, -11, -3, -9, 2, 3, -1, -5, -13, 4, -20],
  [-9, 22, 22, 27, 27, 19, 10, 20, -17, 20, 32, 41, 58, 25, 30, 0, -20, 6, 9, 49, 47, 35, 19, 9, 3, 22, 24, 45, 57, 40, 57, 36, -18, 28, 19, 47, 31, 34, 39, 23, -16, -27, 15, 6, 9, 17, 10, 5, -22, -23, -30, -16, -16, -23, -36, -32, -33, -28, -22, -43, -5, -32, -20, -41],
  [-74, -35, -18, -18, -11, 15, 4, -17, -12, 17, 14, 17, 17, 38, 23, 11, 10, 17, 23, 15, 20, 45, 44, 13, -8, 22, 24, 27, 26, 33, 26, 3, -18, -4, 21, 24, 27, 23, 9, -11, -19, -3, 11, 21, 23, 16, 7, -9, -27, -11, 4, 13, 14, 4, -5, -17, -53, -34, -21, -11, -28, -14, -24, -43],
];
// ------------------------------------------------------------ веса оценки
// Все числа оценки собраны в одном массиве W: для каждого терма пара (миттельшпиль, эндшпиль).
// Значения по умолчанию — PeSTO и ручные; tools/tune.js подбирает их по партиям сильнейших игроков.
const TERMS = [
  ['MAT', 5], ['PST', 6 * 64], ['BPAIR', 1], ['DOUBLED', 1], ['ISOLATED', 1], ['PROTECTED', 1],
  ['PASSED', 8], ['PASSED_KD', 8], ['PASSED_BLOCK', 8],
  ['MOB_N', 9], ['MOB_B', 14], ['MOB_R', 15], ['MOB_Q', 28],
  ['ROOK_OPEN', 1], ['ROOK_SEMI', 1], ['ROOK_7TH', 1], ['SAFETY', 100],
  ['SHIELD_ADV', 1], ['SHIELD_MISS', 1], ['SHIELD_OWNOPEN', 1], ['SHIELD_OPEN', 1], ['KING_EXPOSED', 1], ['TEMPO', 1],
];
const TI = {};
let NTERMS = 0;
for (const [n, c] of TERMS) { TI[n] = NTERMS; NTERMS += c; }
const MOB_OFF = [0, 0, TI.MOB_N, TI.MOB_B, TI.MOB_R, TI.MOB_Q];
// индексы в W (уже умноженные на 2)
const I_BPAIR = 2 * TI.BPAIR, I_DOUBLED = 2 * TI.DOUBLED, I_ISO = 2 * TI.ISOLATED, I_PROT = 2 * TI.PROTECTED;
const I_PASSED = 2 * TI.PASSED, I_PKD = 2 * TI.PASSED_KD, I_PBLK = 2 * TI.PASSED_BLOCK;
const I_MOB = [0, 0, 2 * TI.MOB_N, 2 * TI.MOB_B, 2 * TI.MOB_R, 2 * TI.MOB_Q];
const I_ROPEN = 2 * TI.ROOK_OPEN, I_RSEMI = 2 * TI.ROOK_SEMI, I_R7 = 2 * TI.ROOK_7TH, I_SAFETY = 2 * TI.SAFETY;
const I_SHADV = 2 * TI.SHIELD_ADV, I_SHMISS = 2 * TI.SHIELD_MISS, I_SHOWN = 2 * TI.SHIELD_OWNOPEN, I_SHOPEN = 2 * TI.SHIELD_OPEN;
const I_KEXP = 2 * TI.KING_EXPOSED, I_TEMPO = 2 * TI.TEMPO;
const ATT_WEIGHT = [0, 0, 2, 2, 3, 5, 0];
const SEE_VAL = [0, 100, 320, 330, 500, 900, 20000];

function defaultParams() {
  const P = new Int32Array(2 * NTERMS);
  const set = (i, mg, eg) => { P[2 * i] = mg; P[2 * i + 1] = eg; };
  for (let t = 1; t <= 5; t++) set(TI.MAT + t - 1, MG_VAL[t], EG_VAL[t]);
  for (let t = 1; t <= 6; t++) for (let sq = 0; sq < 64; sq++) set(TI.PST + (t - 1) * 64 + sq, PST_MG[t][sq ^ 56], PST_EG[t][sq ^ 56]);
  set(TI.BPAIR, 25, 45); set(TI.DOUBLED, -6, -12); set(TI.ISOLATED, -8, -10); set(TI.PROTECTED, 5, 6);
  const PMG = [0, 2, 5, 10, 20, 35, 60, 0], PEG = [0, 6, 10, 18, 34, 60, 100, 0], PKD = [0, 0, 0, 1, 3, 5, 8, 0];
  for (let r = 0; r < 8; r++) { set(TI.PASSED + r, PMG[r], PEG[r]); set(TI.PASSED_KD + r, 0, PKD[r]); set(TI.PASSED_BLOCK + r, 0, -(PEG[r] >> 2)); }
  const MMG = [0, 0, 4, 5, 2, 1], MEG = [0, 0, 4, 5, 4, 2], BASE = [0, 0, 4, 7, 7, 14], MAX = [0, 0, 8, 13, 14, 27];
  for (let t = 2; t <= 5; t++) for (let n = 0; n <= MAX[t]; n++) set(MOB_OFF[t] + n, MMG[t] * (n - BASE[t]), MEG[t] * (n - BASE[t]));
  set(TI.ROOK_OPEN, 22, 8); set(TI.ROOK_SEMI, 10, 4); set(TI.ROOK_7TH, 12, 20);
  const SAF = [
    0, 0, 1, 2, 3, 5, 7, 9, 12, 15, 18, 22, 26, 30, 35, 39, 44, 50, 56, 62,
    68, 75, 82, 85, 89, 97, 105, 113, 122, 131, 140, 150, 169, 180, 191, 202, 213, 225, 237, 248,
    260, 272, 283, 295, 307, 319, 330, 342, 354, 366, 377, 389, 401, 412, 424, 436, 448, 459, 471, 483];
  for (let u = 0; u < 100; u++) set(TI.SAFETY + u, ((u < SAF.length ? SAF[u] : 500) * 3) >> 2, 0);
  set(TI.SHIELD_ADV, -8, 0); set(TI.SHIELD_MISS, -22, 0); set(TI.SHIELD_OWNOPEN, -8, 0); set(TI.SHIELD_OPEN, -10, 0);
  set(TI.KING_EXPOSED, -15, 0); set(TI.TEMPO, 12, 12);
  return P;
}

// MG_TAB[piece*128 + sq] — материал + позиционная таблица, сразу по полю 0x88
const MG_TAB = new Int16Array(16 * 128), EG_TAB = new Int16Array(16 * 128);
// Веса, обученные на 3,9 млн позиций из 463 тыс. партий игроков с рейтингом 2400+ (KingBase 2017).
// Получены tools/tune.js (метод Texel), копия — tools/params.json. Пустой массив → веса по умолчанию.
const TUNED = [62,120,297,330,320,344,424,571,1028,962,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-25,14,-17,15,-20,19,-18,10,-8,28,17,19,25,2,-21,-6,-31,1,-17,2,-21,-1,-21,4,0,4,10,4,18,-10,-12,-13,-20,12,-15,16,-3,-7,-4,-10,10,-4,15,2,9,5,-10,-2,-6,34,-2,19,2,12,9,-3,31,4,27,9,26,20,-4,24,-6,84,2,92,24,77,34,65,63,56,66,61,34,82,-4,82,94,166,127,165,65,160,98,136,70,148,125,130,34,162,-12,180,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-104,-29,-22,-56,-51,-22,-32,-17,-14,-24,-24,-24,-17,-50,-24,-64,-31,-42,-47,-18,-12,-18,-4,-17,-1,-12,7,-22,-17,-25,-18,-43,-24,-29,-15,-12,-7,-7,10,14,17,8,2,-14,10,-22,-11,-23,-15,-15,4,-3,11,21,7,27,19,23,21,20,26,7,7,-13,-2,-11,6,2,16,26,51,25,19,30,58,15,18,14,28,-12,-45,-21,54,-18,40,14,67,13,88,3,130,-6,75,-15,47,-37,-68,-21,-36,-5,70,-23,40,2,27,-6,64,-23,8,-23,-14,-48,-167,-57,-88,-35,-34,-11,-47,-25,61,-30,-96,-24,-15,-62,-107,-98,-22,-20,9,-7,-12,-23,-21,-5,-15,-11,-2,-11,-30,-5,-19,-18,5,-14,5,-25,22,-7,-8,-3,2,2,16,-13,22,-13,4,-27,-6,-12,27,0,7,8,8,13,8,15,6,2,14,-8,12,-13,7,-6,10,3,3,17,22,17,27,9,0,8,4,-4,13,-10,-7,-3,5,12,19,11,52,14,30,15,38,10,1,7,-3,3,-12,4,34,-6,39,-1,40,-3,36,0,54,9,40,4,7,10,-26,-8,12,-5,-16,9,-12,-10,29,-4,57,-12,14,-6,-42,-12,-30,-13,4,-19,-81,-7,-37,-6,-25,-5,-42,-8,7,-16,-9,-24,-27,-9,-16,-8,-10,-3,-2,-9,4,-16,-5,-9,-11,2,-17,-18,-47,-8,-29,-15,-21,-7,-16,-10,-9,-21,-6,-19,-7,-16,-64,-2,-47,-2,-28,-2,-19,-5,-19,-5,-4,-12,-5,-13,2,-7,-20,-11,-35,7,-27,9,-15,10,-5,5,0,-4,-5,0,9,-4,-18,-5,-19,18,-6,15,4,19,24,7,19,4,34,4,2,8,-14,9,-1,19,23,14,27,15,37,9,26,10,50,4,66,0,22,7,18,9,23,11,49,9,59,9,76,-5,69,3,28,11,46,5,31,10,41,9,32,19,50,13,62,12,12,17,34,13,45,7,-4,-34,-10,-29,-8,-25,0,-38,-5,-10,-24,-34,-32,-21,-47,-40,-30,-21,-3,-24,5,-32,7,-23,6,-22,11,-28,0,-38,-1,-33,-13,-17,-3,-26,-5,15,-14,6,-3,8,-2,16,13,9,6,4,-12,-19,-25,26,-9,18,-15,48,-9,31,-5,33,0,37,-3,24,-24,4,-23,23,-13,27,-15,50,0,61,12,42,-3,58,-1,38,-12,-17,-13,9,6,12,7,51,30,49,60,39,54,22,53,12,-20,-13,-41,21,-4,35,1,42,-13,61,57,26,25,30,56,1,-27,-7,0,23,26,20,14,29,58,27,46,21,45,12,44,20,-12,-55,47,-34,21,-22,-57,-18,5,-41,-34,-23,16,-32,5,-65,8,-24,10,-11,-7,-4,-53,6,-37,2,-21,-4,11,-11,-9,-24,-13,-20,-11,-2,-22,11,-47,17,-46,20,-36,9,-21,-1,-35,-19,-48,-16,0,1,-26,27,-38,31,-46,32,-45,25,-35,11,-53,-11,-17,-5,-19,28,-11,32,-26,35,-29,35,-24,38,-13,31,-36,5,-9,11,25,23,3,30,-15,22,-18,27,7,50,23,48,-22,15,29,-11,0,20,-19,18,-7,19,-7,20,-3,40,-37,27,-29,12,-65,-73,23,-34,16,-16,-15,-17,-56,-9,-34,16,2,5,13,-17,23,84,-7,-11,-8,-16,6,14,0,0,9,11,6,10,7,25,26,46,49,60,55,74,0,0,0,0,0,-1,-4,3,-3,6,-2,11,-1,16,6,11,0,0,0,0,-1,-3,-4,-2,-8,-11,-9,-17,-5,-28,-9,-47,0,0,-30,-22,-19,-28,-12,-18,-8,3,-2,14,1,24,4,30,10,26,15,19,-36,-44,-33,-44,-26,-33,-21,-21,-16,-7,-12,5,-9,13,-6,15,-4,19,-1,18,11,17,19,21,25,25,30,28,-22,-34,-18,-29,-15,-27,-13,-20,-13,-9,-8,-1,-6,3,-4,9,-1,15,0,21,4,25,8,25,10,28,11,26,14,26,-15,-28,-9,-26,-14,-25,-17,-26,-15,-27,-15,-24,-14,-22,-12,-17,-8,-16,-6,-11,-4,-9,-2,-4,0,3,1,3,2,7,3,8,6,12,6,13,9,14,10,15,9,16,9,17,9,17,10,19,10,20,11,22,12,24,13,26,25,18,10,21,-8,34,0,0,0,0,0,0,1,0,-5,2,4,0,1,4,4,2,10,1,8,4,18,2,18,2,12,2,23,0,21,4,33,2,32,2,33,3,44,2,46,5,55,2,59,2,57,1,64,1,68,4,74,1,79,2,84,1,94,1,103,4,106,1,115,2,129,1,136,0,147,3,152,0,160,1,170,1,177,0,187,1,196,0,204,0,213,0,221,0,230,0,239,0,247,0,256,0,265,0,274,0,282,0,291,0,300,0,309,0,318,0,327,0,336,0,344,0,353,0,362,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,375,0,-6,-2,-7,-8,-12,-8,-20,8,-45,-12,7,7];
let W = TUNED.length === 2 * NTERMS ? Int32Array.from(TUNED) : defaultParams();
function rebuildTables() {
  for (let t = 1; t <= 6; t++) {
    const mm = t <= 5 ? W[2 * (TI.MAT + t - 1)] : 0, me = t <= 5 ? W[2 * (TI.MAT + t - 1) + 1] : 0;
    for (let sq = 0; sq < 128; sq++) {
      if (sq & 0x88) continue;
      const s64 = (sq >> 4) * 8 + (sq & 7);
      const iw = 2 * (TI.PST + (t - 1) * 64 + s64), ib = 2 * (TI.PST + (t - 1) * 64 + (s64 ^ 56));
      MG_TAB[t * 128 + sq] = mm + W[iw]; EG_TAB[t * 128 + sq] = me + W[iw + 1];
      MG_TAB[(8 + t) * 128 + sq] = mm + W[ib]; EG_TAB[(8 + t) * 128 + sq] = me + W[ib + 1];
    }
  }
}
// Подменить веса оценки (массив длины 2*NTERMS). Позиции, созданные раньше, нужно заново загрузить из FEN.
function setParams(arr) {
  if (!arr || arr.length !== 2 * NTERMS) throw new Error('Wrong weight array length');
  W = Int32Array.from(arr);
  rebuildTables();
}
rebuildTables();



// ============================================================== Нейросеть оценки (NNUE)
// Сеть (768 × корзины короля) -> 2xH -> 1 с 8 выходами по числу фигур (см. tools/nn/train.py). Веса — в engine/net.js
// (globalThis.BLIZZARD_NET, base64). Аккумуляторы обновляются лениво: ход только записывает, какие фигуры
// сдвинулись, а сумма пересчитывается, когда позицию действительно нужно оценить.
let NN = null;
// Корзины по положению своего короля (со стороны этой перспективы, доска отражена так, что король —
// на линиях a–d): 0 — a1/b1, 1 — c1/d1, 2 — вторая горизонталь, 3 — дальше. Король на e–h — зеркально.
// 8 и 16 корзин (с 1.0) — те же таблицы, что в core/blizzard.c и tools/nn/trainer.c
function kbTable(kb) {
  const t = new Int8Array(64);
  for (let s = 0; s < 64; s++) {
    const r = s >> 3, f = s & 7;
    t[s] = kb === 8 ? (r === 0 ? (f < 2 ? 0 : 1) : r === 1 ? (f < 2 ? 2 : 3) : r === 2 ? 4 : r === 3 ? 5 : r <= 5 ? 6 : 7)
      : kb === 16 ? (r === 0 ? f : r === 1 ? 4 + f : r === 2 ? 8 + (f >> 1) : r === 3 ? 10 + (f >> 1) : r <= 5 ? 12 + (f >> 1) : 14 + (f >> 1))
      : (r === 0 ? (f < 2 ? 0 : 1) : r === 1 ? 2 : 3);
  }
  return t;
}
let KB_TABLE = kbTable(4);
function loadNet(b64) {
  let bin;
  if (typeof Buffer !== 'undefined') bin = new Uint8Array(Buffer.from(b64, 'base64'));
  else { const s = atob(b64); bin = new Uint8Array(s.length); for (let i = 0; i < s.length; i++) bin[i] = s.charCodeAt(i); }
  const dv = new DataView(bin.buffer, bin.byteOffset, bin.byteLength);
  const magic = dv.getUint32(0, true);
  // 'BLNN' — сеть 0.2 (768 входов), 'BLN2' — с корзинами короля (768 × KB входов)
  if (magic !== 0x4e4e4c42 && magic !== 0x324e4c42) throw new Error('bad net');
  const H = dv.getUint32(4, true), NB = dv.getUint32(8, true);
  let o = 12, KB = 1;
  if (magic === 0x324e4c42) { KB = dv.getUint32(12, true); o = 16; }
  const outScale = dv.getFloat32(o, true), q1 = dv.getFloat32(o + 4, true);
  o += 8;
  const NI = 768 * KB;
  const W1 = new Float32Array(NI * H);
  for (let i = 0; i < NI * H; i++, o += 2) W1[i] = dv.getInt16(o, true) / q1;
  const rd = (n) => { const a = new Float32Array(n); for (let i = 0; i < n; i++, o += 4) a[i] = dv.getFloat32(o, true); return a; };
  const b1 = rd(H), W2 = rd(NB * 2 * H), b2 = rd(NB);
  KB_TABLE = kbTable(KB);
  return quantizeNet({ H, NB, KB, NI, km: KB > 1, outScale, W1f: W1, b1f: b1, W2f: W2, b2 });
}
// Целочисленный вариант: аккумуляторы в Int16 (вдвое меньше памяти на копирование), активация 0..QA.
let NN_QUANT = true;
const QA = 255;
// Масштаб для Int16: как можно крупнее (точнее), но без переполнения — для каждого нейрона
// смещение плюс 32 самых больших по модулю веса должны остаться меньше 32000.
function int16Scale(n) {
  // в аккумулятор попадают строки только одной корзины короля, поэтому 32 самых больших веса — в каждой корзине отдельно
  const H = n.H, KB = n.KB || 1, col = new Float32Array(768);
  let worst = 1e-6;
  for (let h = 0; h < H; h++) {
    for (let b = 0; b < KB; b++) {
      for (let f = 0; f < 768; f++) col[f] = Math.abs(n.W1f[(b * 768 + f) * H + h]);
      col.sort();
      let s = Math.abs(n.b1f[h]);
      for (let k = 0; k < 32; k++) s += col[767 - k];
      if (s > worst) worst = s;
    }
  }
  const qa = Math.min(1024, Math.floor(32000 / worst));
  return qa >= QA ? qa : 0; // слишком крупные веса — считаем в float
}
function quantizeNet(n) {
  if (n.qa16 === undefined) n.qa16 = int16Scale(n);
  if (NN_QUANT && n.qa16) {
    const qa = n.qa = n.qa16;
    n.W1 = Int16Array.from(n.W1f, (x) => Math.max(-32767, Math.min(32767, Math.round(x * qa))));
    n.b1 = Int16Array.from(n.b1f, (x) => Math.round(x * qa));
    n.W2 = Float32Array.from(n.W2f, (x) => x / (qa * qa));
    // выход в целых числах — так же, как nn_ready в core/blizzard.c (результат совпадает до единицы):
    // sq = (clamp(x, 0, qa)² + 256) >> 9, сумма sq · W2Q, затем × K2
    const qq = qa * qa, H = n.H;
    let mx = 1e-12;
    for (let i = 0; i < n.W2.length; i++) { const a = Math.abs(n.W2[i] * qq); if (a > mx) mx = a; }
    const mq = Math.floor((qq + 256) / 512);
    const bound = Math.min(32767, Math.floor(2147483647 / (mq * Math.floor(H / 2))));
    const S = bound / mx;
    n.W2Q = Int16Array.from(n.W2, (x) => Math.floor(x * qq * S + 0.5));
    n.K2 = 512 / (S * qq);
  } else {
    n.qa = 1; n.W1 = n.W1f; n.b1 = n.b1f; n.W2 = n.W2f;
  }
  return n;
}
function setNetQuant(on) { NN_QUANT = !!on; if (NN) quantizeNet(NN); }
// Быстрый путь: аккумуляторы и выход сети на WebAssembly SIMD (tools/wasm/nn.wat) — по 8 чисел за команду.
// Если браузер или Node не умеют SIMD, работает обычный код на JavaScript, результат тот же.
const NN_WASM_B64 = /*NN_WASM*/'AGFzbQEAAAABNAZgBX9/f39/AGAGf39/f39/AGAHf39/f39/fwBgA39/fwBgBX9/f3t7AXtgBX9/f39/AX0CDAEDZW52A21lbQIAAQMJCAABAgMDAwQFBzoHBXVwZDExAAAFdXBkMTIAAQV1cGQyMgACBmFkZFJvdwADBnN1YlJvdwAEBGNvcHkABQVldmFscAAHCrQFCFcBAX8gACAEQQF0aiEFAkADQCAAIAVPDQEgACAB/QAEACAC/QAEAP2OASAD/QAEAP2RAf0LBAAgAEEQaiEAIAFBEGohASACQRBqIQIgA0EQaiEDDAALCwtnAQF/IAAgBUEBdGohBgJAA0AgACAGTw0BIAAgAf0ABAAgAv0ABAD9jgEgA/0ABAD9kQEgBP0ABAD9kQH9CwQAIABBEGohACABQRBqIQEgAkEQaiECIANBEGohAyAEQRBqIQQMAAsLC3cBAX8gACAGQQF0aiEHAkADQCAAIAdPDQEgACAB/QAEACAC/QAEAP2OASAD/QAEAP2OASAE/QAEAP2RASAF/QAEAP2RAf0LBAAgAEEQaiEAIAFBEGohASACQRBqIQIgA0EQaiEDIARBEGohBCAFQRBqIQUMAAsLC0ABAX8gACACQQF0aiEDAkADQCAAIANPDQEgACAA/QAEACAB/QAEAP2OAf0LBAAgAEEQaiEAIAFBEGohAQwACwsLQAEBfyAAIAJBAXRqIQMCQANAIAAgA08NASAAIAD9AAQAIAH9AAQA/ZEB/QsEACAAQRBqIQAgAUEQaiEBDAALCwsPACAAIAEgAkEBdPwKAAALkwECAX8CeyAAIAJBAXRqIQUCQANAIAAgBU8NASAA/QAEAP0MAAAAAAAAAAAAAAAAAAAAAP2YASAD/ZYBIQYgBv2nAf36ASEHIAQgByAH/eYBIAH9AAQA/eYB/eQBIQQgBv2oAf36ASEHIAQgByAH/eYBIAH9AAQQ/eYB/eQBIQQgAEEQaiEAIAFBIGohAQwACwsgBAtTAQJ7IAT9ECEFIAAgAiADIAX9DAAAAAAAAAAAAAAAAAAAAAAQBiEGIAEgAiADQQJ0aiADIAUgBhAGIQYgBv0fACAG/R8BkiAG/R8CIAb9HwOSkgs='/*END*/;
let NN_WASM_MOD, NN_USE_WASM = true;
function nnWasmModule() {
  if (NN_WASM_MOD !== undefined) return NN_WASM_MOD;
  NN_WASM_MOD = null;
  try {
    if (typeof WebAssembly === 'object' && NN_WASM_B64) NN_WASM_MOD = new WebAssembly.Module(b64bytes(NN_WASM_B64));
  } catch (e) { NN_WASM_MOD = null; }
  return NN_WASM_MOD;
}
function setNetWasm(on) { NN_USE_WASM = !!on; }
function initNet() {
  const g = typeof globalThis !== 'undefined' ? globalThis : {};
  if (NN || !g.BLIZZARD_NET) return NN;
  try { NN = loadNet(g.BLIZZARD_NET); } catch (e) { NN = null; }
  return NN;
}
const ACC_SLOTS = MAX_PLY + 16;

// ============================================================== Позиция
class Position {
  constructor() {
    this.board = new Int8Array(128);
    this.kingSq = new Int32Array(2);
    this.mg = new Int32Array(2);
    this.eg = new Int32Array(2);
    this.count = new Int32Array(16);
    // списки фигур каждой стороны: генерация ходов обходит только фигуры, а не все 64 поля
    this.plist = new Int32Array(32); this.pidx = new Int8Array(128); this.pn = new Int32Array(2);
    this.ckLo = 0; this.ckHi = 0; this.ckVal = false; // запомненный шах (inCheck)
    const N = 4096;
    this.uMove = new Int32Array(N); this.uCap = new Int8Array(N); this.uCastle = new Int8Array(N);
    this.uEp = new Int16Array(N); this.uHalf = new Int16Array(N);
    this.uLo = new Int32Array(N); this.uHi = new Int32Array(N);
    this.hLo = new Int32Array(N + 1); this.hHi = new Int32Array(N + 1);
    // рабочие массивы оценки
    this.pa = [new Uint8Array(128), new Uint8Array(128)];
    this.wf = new Int8Array(8); this.bf = new Int8Array(8);
    this.wMin = new Int8Array(8); this.bMax = new Int8Array(8);
    this.seeSq = new Int32Array(40); this.seeP = new Int8Array(40); this.seeGain = new Int32Array(40);
    this.mobZone = new Int32Array(2); this.shCnt = new Int8Array(5);
    this.tmpMoves = new Int32Array(256);
    this.nnOn = false; this.accLock = false; this.acc = null; this.accTop = 0;
    this.pawnKey = 0; // хеш расстановки пешек — для поправки оценки по пешечной структуре
    this.setFen(START_FEN);
  }

  // ---------------------------------------------------- нейросеть: ленивые аккумуляторы
  // Аккумулятор — по слоту на каждый полуход поиска, в слоте две половины: перспектива белых и чёрных.
  // Каждая половина считается отдельно: ключ перспективы (корзина короля и зеркало) меняется только
  // ходом своего короля, и тогда эту половину проще пересчитать с нуля, чем обновлять.
  nnInit() {
    if (!initNet()) return false;
    const kind = NN.qa > 1 ? (NN_USE_WASM && nnWasmModule() ? 'w' : 'i') : 'f';
    if (!this.acc || this.accNet !== NN || this.accKind !== kind || this.accQa !== NN.qa) {
      const H = NN.H;
      this.accNet = NN; this.accKind = kind; this.accQa = NN.qa; this.nw = null;
      if (kind === 'w' && this._wasmInit()) { /* аккумуляторы — в памяти WebAssembly */ }
      else {
        this.accKind = kind === 'w' ? 'i' : kind;
        this.acc = NN.qa > 1 ? new Int16Array(ACC_SLOTS * 2 * H) : new Float32Array(ACC_SLOTS * 2 * H);
        this.fAcc = NN.qa > 1 ? new Int16Array(4 * NN.KB * H) : new Float32Array(4 * NN.KB * H);
      }
      this.accOk = new Uint8Array(ACC_SLOTS * 2);
      this.accKey = new Int8Array(ACC_SLOTS * 2);
      this.chg = new Int32Array(ACC_SLOTS * 6); this.chgN = new Uint8Array(ACC_SLOTS);
      // кэш пересчёта «с нуля» (как finny table в Stockfish): для каждой перспективы и ключа короля —
      // доска и аккумулятор, когда этот ключ встречался последний раз; пересчёт = только разница досок
      this.fBoard = new Int8Array(4 * NN.KB * 64);
      for (let i = 0; i < 4 * NN.KB; i++) this.fAcc.set(NN.b1, i * H);
    }
    this.nnOn = true;
    this.nnRefresh();
    return true;
  }
  // своя память WebAssembly: веса первого слоя, веса выхода, аккумуляторы и кэш (адреса в байтах)
  _wasmInit() {
    try {
      const H = NN.H, al = (x) => (x + 63) & ~63;
      let o = 0;
      const w1 = o; o = al(o + NN.NI * H * 2);
      const w2 = o; o = al(o + NN.NB * 2 * H * 4);
      const ac = o; o = al(o + ACC_SLOTS * 2 * H * 2);
      const fa = o; o = al(o + 4 * NN.KB * H * 2);
      const mem = new WebAssembly.Memory({ initial: Math.ceil(o / 65536) });
      const inst = new WebAssembly.Instance(NN_WASM_MOD, { env: { mem } });
      new Int16Array(mem.buffer, w1, NN.NI * H).set(NN.W1);
      new Float32Array(mem.buffer, w2, NN.NB * 2 * H).set(NN.W2);
      this.acc = new Int16Array(mem.buffer, ac, ACC_SLOTS * 2 * H);
      this.fAcc = new Int16Array(mem.buffer, fa, 4 * NN.KB * H);
      this.nw = inst.exports; this.nwW1 = w1; this.nwW2 = w2; this.nwAc = ac; this.nwFa = fa;
      return true;
    } catch (e) { this.nw = null; return false; }
  }
  // ключ перспективы c (0 — белые): корзина своего короля * 2 + зеркало
  _kkey(c) {
    if (!NN.km) return 0;
    const k = this.kingSq[c];
    let s = (k >> 4) * 8 + (k & 7);
    if (c) s ^= 56;
    const m = (s & 7) >= 4 ? 1 : 0;
    return KB_TABLE[m ? s ^ 7 : s] * 2 + m;
  }
  // строка весов признака «фигура p на поле sq» для перспективы c с ключом key
  _row(p, sq, c, key) {
    let s = (sq >> 4) * 8 + (sq & 7);
    if (c) s ^= 56;
    if (key & 1) s ^= 7;
    return ((key >> 1) * 768 + ((p >> 3) === c ? 0 : 384) + ((p & 7) - 1) * 64 + s) * NN.H;
  }
  // половина c слота t по текущей доске: берём из кэша аккумулятор для этого ключа короля
  // и поправляем его только на те поля, где доска с тех пор изменилась
  _accFull(t, c) {
    const H = NN.H, W1 = NN.W1, b = this.board, fb = this.fBoard, fa = this.fAcc;
    const key = this.accKey[t * 2 + c], ci = c * 2 * NN.KB + key, bo = ci * 64, ao = ci * H;
    const nw = this.nw;
    if (nw) {
      const W = this.nwW1, fo = this.nwFa + ao * 2;
      for (let s = 0; s < 64; s++) {
        const sq = ((s >> 3) << 4) | (s & 7), p = b[sq], q = fb[bo + s];
        if (p === q) continue;
        if (q) nw.subRow(fo, W + this._row(q, sq, c, key) * 2, H);
        if (p) nw.addRow(fo, W + this._row(p, sq, c, key) * 2, H);
        fb[bo + s] = p;
      }
      nw.copy(this.nwAc + (t * 2 + c) * H * 2, fo, H);
      this.accOk[t * 2 + c] = 1;
      return;
    }
    for (let s = 0; s < 64; s++) {
      const sq = ((s >> 3) << 4) | (s & 7), p = b[sq], q = fb[bo + s];
      if (p === q) continue;
      if (q) { const o = this._row(q, sq, c, key); for (let h = 0; h < H; h++) fa[ao + h] -= W1[o + h]; }
      if (p) { const o = this._row(p, sq, c, key); for (let h = 0; h < H; h++) fa[ao + h] += W1[o + h]; }
      fb[bo + s] = p;
    }
    this.acc.set(fa.subarray(ao, ao + H), (t * 2 + c) * H);
    this.accOk[t * 2 + c] = 1;
  }
  nnRefresh() {
    if (!this.acc) return;
    this.accTop = 0;
    for (let c = 0; c < 2; c++) { this.accKey[c] = this._kkey(c); this._accFull(0, c); }
  }
  _accPush() {
    const t = ++this.accTop, a = this.accKey;
    this.accOk[t * 2] = 0; this.accOk[t * 2 + 1] = 0; this.chgN[t] = 0;
    a[t * 2] = a[t * 2 - 2]; a[t * 2 + 1] = a[t * 2 - 1];
  }
  // сделать аккумулятор текущей позиции актуальным
  _accEnsure() {
    const top = this.accTop;
    for (let c = 0; c < 2; c++) if (!this.accOk[top * 2 + c]) this._accEnsureSide(top, c);
  }
  _accEnsureSide(top, c) {
    const ok = this.accOk, keys = this.accKey, key = keys[top * 2 + c];
    let j = top;
    while (!ok[j * 2 + c]) j--;
    // король этой стороны перешёл в другую корзину — проще пересчитать с нуля
    if (keys[j * 2 + c] !== key || top - j > 10) { this._accFull(top, c); return; }
    const H = NN.H, acc = this.acc, W1 = NN.W1, chg = this.chg, nw = this.nw;
    let a0 = 0, a1 = 0, s0 = 0, s1 = 0;
    for (let k = j + 1; k <= top; k++) {
      const dst = (k * 2 + c) * H, src = ((k - 1) * 2 + c) * H;
      const n = this.chgN[k];
      let adds = 0, subs = 0;
      for (let q = 0; q < n; q++) {
        const v = chg[k * 6 + q], o = this._row((v >> 1) & 15, v >> 5, c, key);
        if (v & 1) { if (adds++ === 0) a0 = o; else a1 = o; }
        else { if (subs++ === 0) s0 = o; else s1 = o; }
      }
      if (nw) {
        const W = this.nwW1, d = this.nwAc + dst * 2, sr = this.nwAc + src * 2;
        if (adds === 1 && subs === 1) nw.upd11(d, sr, W + a0 * 2, W + s0 * 2, H);
        else if (adds === 1 && subs === 2) nw.upd12(d, sr, W + a0 * 2, W + s0 * 2, W + s1 * 2, H);
        else if (adds === 2 && subs === 2) nw.upd22(d, sr, W + a0 * 2, W + a1 * 2, W + s0 * 2, W + s1 * 2, H);
        else nw.copy(d, sr, H);
      } else if (adds === 1 && subs === 1) {
        // тихий ход: один проход
        for (let i = 0; i < H; i++) acc[dst + i] = acc[src + i] + W1[a0 + i] - W1[s0 + i];
      } else if (adds === 1 && subs === 2) {
        // взятие
        for (let i = 0; i < H; i++) acc[dst + i] = acc[src + i] + W1[a0 + i] - W1[s0 + i] - W1[s1 + i];
      } else if (adds === 2 && subs === 2) {
        // рокировка
        for (let i = 0; i < H; i++) acc[dst + i] = acc[src + i] + W1[a0 + i] + W1[a1 + i] - W1[s0 + i] - W1[s1 + i];
      } else {
        // нулевой ход: без изменений
        acc.copyWithin(dst, src, src + H);
      }
      // в промежуточном слоте ключ мог быть другим — тогда его половина неверна и не помечается готовой
      ok[k * 2 + c] = keys[k * 2 + c] === key ? 1 : 0;
    }
  }
  // оценка сети со стороны хода, в сантипешках
  nnEval() {
    this._accEnsure();
    const H = NN.H, acc = this.acc, base = this.accTop * 2 * H, c = this.count;
    const uo = base + (this.side ? H : 0), to = base + (this.side ? 0 : H);
    const n = c[1] + c[2] + c[3] + c[4] + c[5] + c[6] + c[9] + c[10] + c[11] + c[12] + c[13] + c[14];
    let bk = (n - 2) >> 2; if (bk > 7) bk = 7; if (bk < 0) bk = 0;
    const W2 = NN.W2, wo = bk * 2 * H, qa = NN.qa;
    if (qa > 1) {
      const W2Q = NN.W2Q;
      let s = 0;
      for (let i = 0; i < H; i++) {
        let x = acc[uo + i];
        if (x > 0) { if (x > qa) x = qa; s += ((x * x + 256) >> 9) * W2Q[wo + i]; }
        x = acc[to + i];
        if (x > 0) { if (x > qa) x = qa; s += ((x * x + 256) >> 9) * W2Q[wo + H + i]; }
      }
      return Math.floor((NN.b2[bk] + s * NN.K2) * NN.outScale + 0.5);
    }
    let s = NN.b2[bk];
    for (let i = 0; i < H; i++) {
      let x = acc[uo + i];
      if (x > 0) { if (x > qa) x = qa; s += x * x * W2[wo + i]; }
      x = acc[to + i];
      if (x > 0) { if (x > qa) x = qa; s += x * x * W2[wo + H + i]; }
    }
    return Math.round(s * NN.outScale);
  }

  // ---------------------------------------------------- низкоуровневые операции
  _add(sq, p) {
    if (this.nnOn && !this.accLock) { const t = this.accTop; this.chg[t * 6 + this.chgN[t]++] = (sq << 5) | (p << 1) | 1; }
    this.board[sq] = p;
    const i = p * 128 + sq, c = p >> 3;
    if ((p & 7) === PAWN) this.pawnKey ^= Z_PIECE_LO[i];
    const k = this.pn[c]++;
    this.plist[(c << 4) + k] = sq; this.pidx[sq] = k;
    this.hashLo ^= Z_PIECE_LO[i]; this.hashHi ^= Z_PIECE_HI[i];
    this.mg[c] += MG_TAB[i]; this.eg[c] += EG_TAB[i];
    this.phase += PHASE_INC[p & 7];
    this.count[p]++;
  }
  _remove(sq) {
    const p = this.board[sq];
    if (this.nnOn && !this.accLock) { const t = this.accTop; this.chg[t * 6 + this.chgN[t]++] = (sq << 5) | (p << 1); }
    this.board[sq] = 0;
    const i = p * 128 + sq, c = p >> 3;
    if ((p & 7) === PAWN) this.pawnKey ^= Z_PIECE_LO[i];
    const k = this.pidx[sq], last = --this.pn[c], ls = this.plist[(c << 4) + last];
    this.plist[(c << 4) + k] = ls; this.pidx[ls] = k;
    this.hashLo ^= Z_PIECE_LO[i]; this.hashHi ^= Z_PIECE_HI[i];
    this.mg[c] -= MG_TAB[i]; this.eg[c] -= EG_TAB[i];
    this.phase -= PHASE_INC[p & 7];
    this.count[p]--;
  }

  // ---------------------------------------------------------------- FEN
  setFen(fen) {
    const parts = String(fen).trim().split(/\s+/);
    if (parts.length < 2) throw new Error('Invalid FEN');
    this.accLock = true;
    this.board.fill(0); this.count.fill(0); this.pn.fill(0);
    this.mg[0] = this.mg[1] = this.eg[0] = this.eg[1] = 0;
    this.phase = 0; this.hashLo = 0; this.hashHi = 0; this.pawnKey = 0;
    this.kingSq[0] = this.kingSq[1] = -1;
    let rank = 7, file = 0, kings = [0, 0];
    for (const ch of parts[0]) {
      if (ch === '/') { rank--; file = 0; continue; }
      if (ch >= '1' && ch <= '8') { file += ch.charCodeAt(0) - 48; continue; }
      const p = PIECE_FROM_CHAR[ch];
      if (!p || file > 7 || rank < 0) throw new Error('Invalid FEN');
      const sq = rank * 16 + file;
      this._add(sq, p);
      if ((p & 7) === KING) { this.kingSq[p >> 3] = sq; kings[p >> 3]++; }
      file++;
    }
    if (kings[0] !== 1 || kings[1] !== 1) throw new Error('Each side must have exactly one king');
    this.side = parts[1] === 'b' ? BLACK : WHITE;
    let c = 0;
    const cs = parts[2] || '-';
    if (cs.includes('K') && this.board[4] === 6 && this.board[7] === 4) c |= 1;
    if (cs.includes('Q') && this.board[4] === 6 && this.board[0] === 4) c |= 2;
    if (cs.includes('k') && this.board[116] === 14 && this.board[119] === 12) c |= 4;
    if (cs.includes('q') && this.board[116] === 14 && this.board[112] === 12) c |= 8;
    this.castle = c;
    this.ep = -1;
    const ep = parseSq(parts[3] || '-');
    if (ep >= 0) {
      const b = this.board;
      if (this.side === WHITE && (ep >> 4) === 5) {
        if ((!((ep - 15) & 0x88) && b[ep - 15] === 1) || (!((ep - 17) & 0x88) && b[ep - 17] === 1)) this.ep = ep;
      } else if (this.side === BLACK && (ep >> 4) === 2) {
        if ((!((ep + 15) & 0x88) && b[ep + 15] === 9) || (!((ep + 17) & 0x88) && b[ep + 17] === 9)) this.ep = ep;
      }
    }
    this.halfmove = parseInt(parts[4], 10) || 0;
    this.fullmove = parseInt(parts[5], 10) || 1;
    if (this.side === BLACK) { this.hashLo ^= Z_SIDE_LO; this.hashHi ^= Z_SIDE_HI; }
    this.hashLo ^= Z_CASTLE_LO[this.castle]; this.hashHi ^= Z_CASTLE_HI[this.castle];
    if (this.ep >= 0) { this.hashLo ^= Z_EP_LO[this.ep & 7]; this.hashHi ^= Z_EP_HI[this.ep & 7]; }
    this.ply = 0;
    this.hLo[0] = this.hashLo; this.hHi[0] = this.hashHi;
    if (this.isAttacked(this.kingSq[this.side ^ 1], this.side)) throw new Error('The side not to move is in check');
    this.accLock = false;
    if (this.nnOn) this.nnRefresh();
    return this;
  }

  fen() {
    const b = this.board;
    let s = '';
    for (let r = 7; r >= 0; r--) {
      let empty = 0;
      for (let f = 0; f < 8; f++) {
        const p = b[r * 16 + f];
        if (!p) { empty++; continue; }
        if (empty) { s += empty; empty = 0; }
        s += PIECE_CHARS[p];
      }
      if (empty) s += empty;
      if (r) s += '/';
    }
    let cs = '';
    if (this.castle & 1) cs += 'K'; if (this.castle & 2) cs += 'Q';
    if (this.castle & 4) cs += 'k'; if (this.castle & 8) cs += 'q';
    return `${s} ${this.side ? 'b' : 'w'} ${cs || '-'} ${this.ep >= 0 ? sqName(this.ep) : '-'} ${this.halfmove} ${this.fullmove}`;
  }

  clone() { const p = new Position(); p.setFen(this.fen()); return p; }

  // ---------------------------------------------------------------- атаки
  // Бьёт ли сторона by поле sq: пешки — напрямую, остальные фигуры — по списку фигур и таблице направлений
  isAttacked(sq, by) {
    const b = this.board;
    let s;
    if (by === WHITE) {
      s = sq - 15; if (!(s & 0x88) && b[s] === 1) return true;
      s = sq - 17; if (!(s & 0x88) && b[s] === 1) return true;
    } else {
      s = sq + 15; if (!(s & 0x88) && b[s] === 9) return true;
      s = sq + 17; if (!(s & 0x88) && b[s] === 9) return true;
    }
    const pl = this.plist, base = by << 4, n = this.pn[by];
    for (let i = 0; i < n; i++) {
      const f = pl[base + i], idx = sq - f + 119, a = ATT_MASK[idx];
      if (!a) continue;
      const t = b[f] & 7;
      if (t === KNIGHT) { if (a & 1) return true; continue; }
      if (t === KING) { if (a & 2) return true; continue; }
      if (t === PAWN || !(a & (t === BISHOP ? 4 : t === ROOK ? 8 : 12))) continue;
      const d = ATT_DIR[idx];
      s = f + d;
      while (s !== sq && !b[s]) s += d;
      if (s === sq) return true;
    }
    return false;
  }
  // шах своему королю; результат запоминается для текущей позиции (по хешу)
  inCheck() {
    if (this.ckLo === this.hashLo && this.ckHi === this.hashHi) return this.ckVal;
    const v = this.isAttacked(this.kingSq[this.side], this.side ^ 1);
    this.ckLo = this.hashLo; this.ckHi = this.hashHi; this.ckVal = v;
    return v;
  }

  // ---------------------------------------------------------------- генерация
  // Псевдолегальные ходы в list начиная с n. quiets=false — только взятия и превращения в ферзя.
  genMoves(list, n, quiets) {
    const b = this.board, us = this.side, them = us ^ 1;
    const fwd = us ? -16 : 16;
    const startRank = us ? 6 : 1, promoRank = us ? 0 : 7;
    const pl = this.plist, pbase = us << 4, pcount = this.pn[us];
    for (let pi = 0; pi < pcount; pi++) {
      const sq = pl[pbase + pi];
      const p = b[sq];
      const t = p & 7;
      if (t === PAWN) {
        let to = sq + fwd;
        if (!b[to]) {
          if ((to >> 4) === promoRank) {
            list[n++] = mkMove(sq, to, QUEEN, F_NONE, 0);
            if (quiets) {
              list[n++] = mkMove(sq, to, KNIGHT, F_NONE, 0);
              list[n++] = mkMove(sq, to, ROOK, F_NONE, 0);
              list[n++] = mkMove(sq, to, BISHOP, F_NONE, 0);
            }
          } else if (quiets) {
            list[n++] = mkMove(sq, to, 0, F_NONE, 0);
            if ((sq >> 4) === startRank && !b[to + fwd]) list[n++] = mkMove(sq, to + fwd, 0, F_DOUBLE, 0);
          }
        }
        for (let k = -1; k <= 1; k += 2) {
          to = sq + fwd + k;
          if (to & 0x88) continue;
          const q = b[to];
          if (q && (q >> 3) === them) {
            if ((to >> 4) === promoRank) {
              list[n++] = mkMove(sq, to, QUEEN, F_NONE, 1);
              if (quiets) {
                list[n++] = mkMove(sq, to, KNIGHT, F_NONE, 1);
                list[n++] = mkMove(sq, to, ROOK, F_NONE, 1);
                list[n++] = mkMove(sq, to, BISHOP, F_NONE, 1);
              }
            } else list[n++] = mkMove(sq, to, 0, F_NONE, 1);
          } else if (to === this.ep) {
            list[n++] = mkMove(sq, to, 0, F_EP, 1);
          }
        }
      } else if (t === KNIGHT || t === KING) {
        const offs = t === KNIGHT ? KNIGHT_OFF : KING_OFF;
        for (let i = 0; i < 8; i++) {
          const to = sq + offs[i];
          if (to & 0x88) continue;
          const q = b[to];
          if (!q) { if (quiets) list[n++] = mkMove(sq, to, 0, F_NONE, 0); }
          else if ((q >> 3) === them) list[n++] = mkMove(sq, to, 0, F_NONE, 1);
        }
      } else {
        for (let i = 0; i < 8; i++) {
          let d;
          if (i < 4) { if (t === ROOK) continue; d = DIAG[i]; }
          else { if (t === BISHOP) break; d = ORTHO[i - 4]; }
          let to = sq + d;
          while (!(to & 0x88)) {
            const q = b[to];
            if (!q) { if (quiets) list[n++] = mkMove(sq, to, 0, F_NONE, 0); }
            else { if ((q >> 3) === them) list[n++] = mkMove(sq, to, 0, F_NONE, 1); break; }
            to += d;
          }
        }
      }
    }
    // рокировки
    if (quiets && this.castle) {
      if (us === WHITE) {
        if ((this.castle & 1) && !b[5] && !b[6] && !this.isAttacked(4, BLACK) && !this.isAttacked(5, BLACK))
          list[n++] = mkMove(4, 6, 0, F_CASTLE, 0);
        if ((this.castle & 2) && !b[3] && !b[2] && !b[1] && !this.isAttacked(4, BLACK) && !this.isAttacked(3, BLACK))
          list[n++] = mkMove(4, 2, 0, F_CASTLE, 0);
      } else {
        if ((this.castle & 4) && !b[117] && !b[118] && !this.isAttacked(116, WHITE) && !this.isAttacked(117, WHITE))
          list[n++] = mkMove(116, 118, 0, F_CASTLE, 0);
        if ((this.castle & 8) && !b[115] && !b[114] && !b[113] && !this.isAttacked(116, WHITE) && !this.isAttacked(115, WHITE))
          list[n++] = mkMove(116, 114, 0, F_CASTLE, 0);
      }
    }
    return n;
  }

  // ---------------------------------------------------------------- ходы
  // Делает ход. Если ход нелегален (король остаётся под боем) — откатывает и возвращает false.
  // safe = своему королю до хода не было шаха: тогда ход фигурой не с линии короля легален без проверки
  make(m, safe = false) {
    const b = this.board;
    const from = m & 127, to = (m >> 7) & 127, promo = (m >> 14) & 7, flag = (m >> 17) & 7;
    const us = this.side, them = us ^ 1;
    const p = b[from];
    const ply = this.ply;
    if (this.nnOn) this._accPush();
    this.uMove[ply] = m; this.uCastle[ply] = this.castle; this.uEp[ply] = this.ep;
    this.uHalf[ply] = this.halfmove; this.uLo[ply] = this.hashLo; this.uHi[ply] = this.hashHi;
    if (this.ep >= 0) { this.hashLo ^= Z_EP_LO[this.ep & 7]; this.hashHi ^= Z_EP_HI[this.ep & 7]; }
    this.hashLo ^= Z_CASTLE_LO[this.castle]; this.hashHi ^= Z_CASTLE_HI[this.castle];
    let cap = 0;
    if (flag === F_EP) {
      const cs = us === WHITE ? to - 16 : to + 16;
      cap = b[cs]; this._remove(cs);
    } else if (b[to]) { cap = b[to]; this._remove(to); }
    this.uCap[ply] = cap;
    this._remove(from);
    this._add(to, promo ? ((us << 3) | promo) : p);
    if (flag === F_CASTLE) {
      if (to > from) { const r = b[from + 3]; this._remove(from + 3); this._add(from + 1, r); }
      else { const r = b[from - 4]; this._remove(from - 4); this._add(from - 1, r); }
    }
    if ((p & 7) === KING) {
      this.kingSq[us] = to;
      if (this.nnOn && NN.km) this.accKey[this.accTop * 2 + us] = this._kkey(us);
    }
    this.castle &= CASTLE_MASK[from] & CASTLE_MASK[to];
    this.hashLo ^= Z_CASTLE_LO[this.castle]; this.hashHi ^= Z_CASTLE_HI[this.castle];
    this.ep = -1;
    if (flag === F_DOUBLE) {
      const ep = (from + to) >> 1, ePawn = (them << 3) | PAWN;
      if ((!((to - 1) & 0x88) && b[to - 1] === ePawn) || (!((to + 1) & 0x88) && b[to + 1] === ePawn)) {
        this.ep = ep; this.hashLo ^= Z_EP_LO[ep & 7]; this.hashHi ^= Z_EP_HI[ep & 7];
      }
    }
    this.halfmove = ((p & 7) === PAWN || cap) ? 0 : this.halfmove + 1;
    if (us === BLACK) this.fullmove++;
    this.side = them;
    this.hashLo ^= Z_SIDE_LO; this.hashHi ^= Z_SIDE_HI;
    this.ply = ply + 1;
    this.hLo[ply + 1] = this.hashLo; this.hHi[ply + 1] = this.hashHi;
    if (safe && (p & 7) !== KING && flag !== F_EP && !LINE[this.kingSq[us] - from + 119]) return true;
    if (this.isAttacked(this.kingSq[us], them)) { this.unmake(); return false; }
    return true;
  }

  unmake() {
    const ply = --this.ply;
    const m = this.uMove[ply];
    const from = m & 127, to = (m >> 7) & 127, promo = (m >> 14) & 7, flag = (m >> 17) & 7;
    const us = this.side ^ 1;
    this.side = us;
    const b = this.board;
    const p = promo ? ((us << 3) | PAWN) : b[to];
    this.accLock = true;
    this._remove(to);
    this._add(from, p);
    if (flag === F_CASTLE) {
      if (to > from) { const r = b[from + 1]; this._remove(from + 1); this._add(from + 3, r); }
      else { const r = b[from - 1]; this._remove(from - 1); this._add(from - 4, r); }
    }
    const cap = this.uCap[ply];
    if (cap) this._add(flag === F_EP ? (us === WHITE ? to - 16 : to + 16) : to, cap);
    if ((p & 7) === KING) this.kingSq[us] = from;
    this.accLock = false;
    if (this.nnOn) this.accTop--;
    this.castle = this.uCastle[ply]; this.ep = this.uEp[ply]; this.halfmove = this.uHalf[ply];
    if (us === BLACK) this.fullmove--;
    this.hashLo = this.uLo[ply]; this.hashHi = this.uHi[ply];
  }

  makeNull() {
    const ply = this.ply;
    this.uMove[ply] = 0; this.uEp[ply] = this.ep; this.uHalf[ply] = this.halfmove;
    this.uLo[ply] = this.hashLo; this.uHi[ply] = this.hashHi; this.uCastle[ply] = this.castle;
    if (this.ep >= 0) { this.hashLo ^= Z_EP_LO[this.ep & 7]; this.hashHi ^= Z_EP_HI[this.ep & 7]; }
    this.ep = -1;
    this.side ^= 1;
    this.hashLo ^= Z_SIDE_LO; this.hashHi ^= Z_SIDE_HI;
    this.halfmove = 0; // повторения не считаем через нулевой ход
    if (this.nnOn) this._accPush();
    this.ply = ply + 1;
    this.hLo[ply + 1] = this.hashLo; this.hHi[ply + 1] = this.hashHi;
  }
  unmakeNull() {
    const ply = --this.ply;
    if (this.nnOn) this.accTop--;
    this.side ^= 1;
    this.ep = this.uEp[ply]; this.halfmove = this.uHalf[ply];
    this.hashLo = this.uLo[ply]; this.hashHi = this.uHi[ply];
  }

  // ---------------------------------------------------------------- состояние
  isRepetition() {
    const stop = Math.max(0, this.ply - this.halfmove);
    for (let i = this.ply - 2; i >= stop; i -= 2)
      if (this.hLo[i] === this.hashLo && this.hHi[i] === this.hashHi) return true;
    return false;
  }
  repetitionCount() {
    let n = 1;
    const stop = Math.max(0, this.ply - this.halfmove);
    for (let i = this.ply - 2; i >= stop; i -= 2)
      if (this.hLo[i] === this.hashLo && this.hHi[i] === this.hashHi) n++;
    return n;
  }
  insufficientMaterial() {
    const c = this.count;
    if (c[1] || c[9] || c[4] || c[12] || c[5] || c[13]) return false;
    return c[2] + c[3] + c[10] + c[11] <= 1;
  }
  hasNonPawn(side) {
    const c = this.count, o = side << 3;
    return c[o + 2] + c[o + 3] + c[o + 4] + c[o + 5] > 0;
  }

  legalMoves() {
    const buf = new Int32Array(256);
    const n = this.genMoves(buf, 0, true);
    const out = [];
    for (let i = 0; i < n; i++) if (this.make(buf[i])) { this.unmake(); out.push(buf[i]); }
    return out;
  }
  hasLegalMove() {
    const buf = this.tmpMoves;
    const n = this.genMoves(buf, 0, true);
    for (let i = 0; i < n; i++) if (this.make(buf[i])) { this.unmake(); return true; }
    return false;
  }

  // Итог партии: null, либо { result: '1-0'|'0-1'|'1/2-1/2', reason }
  gameResult() {
    if (!this.hasLegalMove()) {
      if (this.inCheck()) return { result: this.side === WHITE ? '0-1' : '1-0', reason: 'checkmate' };
      return { result: '1/2-1/2', reason: 'stalemate' };
    }
    if (this.insufficientMaterial()) return { result: '1/2-1/2', reason: 'material' };
    if (this.halfmove >= 100) return { result: '1/2-1/2', reason: 'fifty' };
    if (this.repetitionCount() >= 3) return { result: '1/2-1/2', reason: 'repetition' };
    return null;
  }

  // ---------------------------------------------------------------- нотация
  moveToUci(m) {
    if (!m) return '0000';
    const promo = (m >> 14) & 7;
    return sqName(m & 127) + sqName((m >> 7) & 127) + (promo ? ' pnbrqk'[promo] : '');
  }
  uciToMove(str) {
    if (!str) return 0;
    const legal = this.legalMoves();
    for (const m of legal) if (this.moveToUci(m) === str) return m;
    // допускаем превращение без буквы как ферзя
    for (const m of legal) if (this.moveToUci(m) === str + 'q') return m;
    return 0;
  }
  moveToSan(m) {
    const b = this.board;
    const from = m & 127, to = (m >> 7) & 127, promo = (m >> 14) & 7, flag = (m >> 17) & 7;
    const p = b[from], t = p & 7;
    let s;
    if (flag === F_CASTLE) s = to > from ? 'O-O' : 'O-O-O';
    else {
      const capture = (m >> 20) & 1;
      if (t === PAWN) {
        s = capture ? 'abcdefgh'[from & 7] + 'x' + sqName(to) : sqName(to);
        if (promo) s += '=' + 'PNBRQK'[promo - 1];
      } else {
        s = 'PNBRQK'[t - 1];
        const legal = this.legalMoves();
        let sameFile = false, sameRank = false, ambiguous = false;
        for (const o of legal) {
          const of = o & 127;
          if (of === from || ((o >> 7) & 127) !== to || b[of] !== p) continue;
          ambiguous = true;
          if ((of & 7) === (from & 7)) sameFile = true;
          if ((of >> 4) === (from >> 4)) sameRank = true;
        }
        if (ambiguous) {
          if (!sameFile) s += 'abcdefgh'[from & 7];
          else if (!sameRank) s += (from >> 4) + 1;
          else s += sqName(from);
        }
        if (capture) s += 'x';
        s += sqName(to);
      }
    }
    if (this.make(m)) {
      if (this.inCheck()) s += this.hasLegalMove() ? '+' : '#';
      this.unmake();
    }
    return s;
  }
  sanToMove(san) {
    const clean = String(san).replace(/[+#!?]/g, '').replace(/0/g, 'O');
    for (const m of this.legalMoves()) if (this.moveToSan(m).replace(/[+#]/g, '') === clean) return m;
    return 0;
  }

  // Разбор SAN «с допуском»: лишняя/недостающая неоднозначность, 0-0, e.p., длинная нотация e2e4
  parseSan(san) {
    let s = String(san).trim().replace(/\s*e\.p\.?$/i, '').replace(/[+#?!]+/g, '');
    if (/^[0O]-[0O]-[0O]$/.test(s)) s = 'O-O-O';
    else if (/^[0O]-[0O]$/.test(s)) s = 'O-O';
    const buf = this.tmpMoves;
    const n = this.genMoves(buf, 0, true);
    const legal = (m) => { if (!this.make(m)) return false; this.unmake(); return true; };
    if (s === 'O-O' || s === 'O-O-O') {
      for (let i = 0; i < n; i++) {
        const m = buf[i];
        if (((m >> 17) & 7) !== F_CASTLE) continue;
        if ((((m >> 7) & 127) > (m & 127)) === (s === 'O-O') && legal(m)) return m;
      }
      return 0;
    }
    const r = /^([NBRQK])?([a-h])?([1-8])?[x:-]?([a-h][1-8])(?:=?([NBRQnbrq]))?$/.exec(s);
    if (!r) return 0;
    const type = r[1] ? 'PNBRQK'.indexOf(r[1]) + 1 : PAWN;
    const ff = r[2] ? r[2].charCodeAt(0) - 97 : -1, fr = r[3] ? +r[3] - 1 : -1;
    const to = parseSq(r[4]);
    let promo = r[5] ? ' pnbrqk'.indexOf(r[5].toLowerCase()) : 0;
    const lastRank = this.side === WHITE ? 7 : 0;
    if (type === PAWN && (to >> 4) === lastRank && !promo) promo = QUEEN;
    const cands = [];
    for (let i = 0; i < n; i++) {
      const m = buf[i], from = m & 127;
      if (((m >> 7) & 127) !== to || (this.board[from] & 7) !== type) continue;
      if (ff >= 0 && (from & 7) !== ff) continue;
      if (fr >= 0 && (from >> 4) !== fr) continue;
      if (((m >> 14) & 7) !== promo) continue;
      cands.push(m);
    }
    for (const m of cands) if (legal(m)) return m;
    return 0;
  }

  // ================================================================ ОЦЕНКА
  // Пешечный проход: файлы, крайние пешки, поля, которые бьют пешки.
  _pawnScan() {
    const b = this.board;
    const pa0 = this.pa[0], pa1 = this.pa[1];
    pa0.fill(0); pa1.fill(0);
    const wf = this.wf, bf = this.bf, wMin = this.wMin, bMax = this.bMax;
    wf.fill(0); bf.fill(0); wMin.fill(8); bMax.fill(-1);
    for (let sq = 16; sq < 104; sq++) {
      if (sq & 0x88) { sq += 7; continue; }
      const p = b[sq];
      if (p === 1) {
        const f = sq & 7, r = sq >> 4;
        wf[f]++; if (r < wMin[f]) wMin[f] = r;
        if (f > 0) pa0[sq + 15] = 1;
        if (f < 7) pa0[sq + 17] = 1;
      } else if (p === 9) {
        const f = sq & 7, r = sq >> 4;
        bf[f]++; if (r > bMax[f]) bMax[f] = r;
        if (f > 0) pa1[sq - 17] = 1;
        if (f < 7) pa1[sq - 15] = 1;
      }
    }
  }

  // Подвижность фигуры и число атакованных полей возле вражеского короля → this.mobZone = [mob, zone]
  _mobility(sq, t, c) {
    const b = this.board;
    const ePA = c === WHITE ? this.pa[1] : this.pa[0];
    const ek = this.kingSq[c ^ 1], ekf = ek & 7, ekr = ek >> 4;
    const fwdZone = c === WHITE ? -2 : 2;
    let mob = 0, zone = 0;
    if (t === KNIGHT) {
      for (let i = 0; i < 8; i++) {
        const s = sq + KNIGHT_OFF[i];
        if (s & 0x88) continue;
        const q = b[s];
        if (q && (q >> 3) === c) continue;
        if (!ePA[s]) mob++;
        const df = (s & 7) - ekf, dr = (s >> 4) - ekr;
        if (df <= 1 && df >= -1 && ((dr <= 1 && dr >= -1) || dr === fwdZone)) zone++;
      }
    } else {
      const d0 = t === ROOK ? 4 : 0, d1 = t === BISHOP ? 4 : 8;
      for (let i = d0; i < d1; i++) {
        const d = i < 4 ? DIAG[i] : ORTHO[i - 4];
        let s = sq + d;
        while (!(s & 0x88)) {
          const q = b[s];
          if (q && (q >> 3) === c) break;
          if (!ePA[s]) mob++;
          const df = (s & 7) - ekf, dr = (s >> 4) - ekr;
          if (df <= 1 && df >= -1 && ((dr <= 1 && dr >= -1) || dr === fwdZone)) zone++;
          if (q) break;
          s += d;
        }
      }
    }
    this.mobZone[0] = mob; this.mobZone[1] = zone;
  }

  // Пешечный щит короля: счётчики [продвинутых, отсутствующих, своих открытых линий, полностью открытых, король ушёл]
  _shield(c, kf, kr) {
    const b = this.board, sh = this.shCnt;
    sh.fill(0);
    const rel = c === WHITE ? kr : 7 - kr;
    if (rel > 1) { sh[4] = 1; return; }
    const pawn = c === WHITE ? 1 : 9, dir = c === WHITE ? 16 : -16;
    const own = c === WHITE ? this.wf : this.bf, opp = c === WHITE ? this.bf : this.wf;
    for (let f = Math.max(0, kf - 1); f <= Math.min(7, kf + 1); f++) {
      const base = kr * 16 + f;
      if (b[base + dir] === pawn) { /* на месте */ }
      else if (!((base + 2 * dir) & 0x88) && b[base + 2 * dir] === pawn) sh[0]++;
      else sh[1]++;
      if (own[f] === 0) { sh[2]++; if (opp[f] === 0) sh[3]++; }
    }
  }

  // Особые эндшпили, где линейная оценка масштабируется (для обучения такие позиции пропускаются)
  _isSpecialEnding() {
    const c = this.count;
    if (c[1] === 0 || c[9] === 0) return true;
    return c[3] === 1 && c[11] === 1 && c[2] + c[4] + c[5] + c[10] + c[12] + c[13] === 0;
  }

  // Возвращает оценку в сантипешках с точки зрения стороны, которая ходит.
  // Оценка позиции со стороны хода: нейросеть, если она загружена и включена, иначе ручная оценка.
  evaluate() {
    if (!this.nnOn) return this.hceEvaluate();
    let score = this.nnEval();
    if (this.side !== WHITE) score = -score;
    const cnt = this.count;
    const wP = cnt[1], wN = cnt[2], wB = cnt[3], wR = cnt[4], wQ = cnt[5];
    const bP = cnt[9], bN = cnt[10], bB = cnt[11], bR = cnt[12], bQ = cnt[13];
    const wk = this.kingSq[0], bk = this.kingSq[1];
    // те же эндшпильные поправки, что и в ручной оценке: без пешек мало фигур — почти ничья; добивание одинокого короля
    const wNpm = 3 * (wN + wB) + 5 * wR + 9 * wQ, bNpm = 3 * (bN + bB) + 5 * bR + 9 * bQ;
    if (score > 0) {
      if (wP === 0) {
        if (wNpm <= 3) score >>= 4;
        else if (wN === 2 && wNpm === 6 && bNpm === 0) score >>= 3;
        else if (wNpm - bNpm <= 3) score >>= 2;
      }
      if (bP === 0 && wNpm >= bNpm + 5 && bNpm <= 3) score += mopUp(wk, bk);
    } else if (score < 0) {
      if (bP === 0) {
        if (bNpm <= 3) score = -((-score) >> 4);
        else if (bN === 2 && bNpm === 6 && wNpm === 0) score = -((-score) >> 3);
        else if (bNpm - wNpm <= 3) score = -((-score) >> 2);
      }
      if (wP === 0 && bNpm >= wNpm + 5 && wNpm <= 3) score -= mopUp(bk, wk);
    }
    if (score > 20000) score = 20000; else if (score < -20000) score = -20000;
    return this.side === WHITE ? score : -score;
  }

  hceEvaluate() {
    const b = this.board, cnt = this.count, w = W;
    const wP = cnt[1], wN = cnt[2], wB = cnt[3], wR = cnt[4], wQ = cnt[5];
    const bP = cnt[9], bN = cnt[10], bB = cnt[11], bR = cnt[12], bQ = cnt[13];
    let mg = this.mg[0] - this.mg[1];
    let eg = this.eg[0] - this.eg[1];
    if (wB >= 2) { mg += w[I_BPAIR]; eg += w[I_BPAIR + 1]; }
    if (bB >= 2) { mg -= w[I_BPAIR]; eg -= w[I_BPAIR + 1]; }

    this._pawnScan();
    const pa0 = this.pa[0], pa1 = this.pa[1], wf = this.wf, bf = this.bf, wMin = this.wMin, bMax = this.bMax;
    const wk = this.kingSq[0], bk = this.kingSq[1];
    const wkf = wk & 7, wkr = wk >> 4, bkf = bk & 7, bkr = bk >> 4;
    let attU0 = 0, attN0 = 0, attU1 = 0, attN1 = 0;
    let wBishopCol = -1, bBishopCol = -1;
    const mz = this.mobZone;

    for (let sq = 0; sq < 120; sq++) {
      if (sq & 0x88) { sq += 7; continue; }
      const p = b[sq];
      if (!p) continue;
      const t = p & 7, c = p >> 3, f = sq & 7, r = sq >> 4;
      if (t === PAWN) {
        if (c === WHITE) {
          if (wf[f] > 1) { mg += w[I_DOUBLED]; eg += w[I_DOUBLED + 1]; }
          if ((f === 0 || wf[f - 1] === 0) && (f === 7 || wf[f + 1] === 0)) { mg += w[I_ISO]; eg += w[I_ISO + 1]; }
          if (pa0[sq]) { mg += w[I_PROT]; eg += w[I_PROT + 1]; }
          if ((f === 0 || bMax[f - 1] <= r) && bMax[f] <= r && (f === 7 || bMax[f + 1] <= r)) {
            const i = 2 * r, a = sq + 16, kd = 2 * sqDist(a, bk) - sqDist(a, wk);
            mg += w[I_PASSED + i] + kd * w[I_PKD + i]; eg += w[I_PASSED + i + 1] + kd * w[I_PKD + i + 1];
            if (b[a]) { mg += w[I_PBLK + i]; eg += w[I_PBLK + i + 1]; }
          }
        } else {
          if (bf[f] > 1) { mg -= w[I_DOUBLED]; eg -= w[I_DOUBLED + 1]; }
          if ((f === 0 || bf[f - 1] === 0) && (f === 7 || bf[f + 1] === 0)) { mg -= w[I_ISO]; eg -= w[I_ISO + 1]; }
          if (pa1[sq]) { mg -= w[I_PROT]; eg -= w[I_PROT + 1]; }
          if ((f === 0 || wMin[f - 1] >= r) && wMin[f] >= r && (f === 7 || wMin[f + 1] >= r)) {
            const i = 2 * (7 - r), a = sq - 16, kd = 2 * sqDist(a, wk) - sqDist(a, bk);
            mg -= w[I_PASSED + i] + kd * w[I_PKD + i]; eg -= w[I_PASSED + i + 1] + kd * w[I_PKD + i + 1];
            if (b[a]) { mg -= w[I_PBLK + i]; eg -= w[I_PBLK + i + 1]; }
          }
        }
        continue;
      }
      if (t === KING) continue;
      if (t === BISHOP) { if (c === WHITE) wBishopCol = (f + r) & 1; else bBishopCol = (f + r) & 1; }
      this._mobility(sq, t, c);
      const mi = I_MOB[t] + 2 * mz[0];
      let xmg = w[mi], xeg = w[mi + 1];
      if (t === ROOK) {
        const own = c === WHITE ? wf : bf, opp = c === WHITE ? bf : wf;
        if (own[f] === 0) {
          if (opp[f] === 0) { xmg += w[I_ROPEN]; xeg += w[I_ROPEN + 1]; }
          else { xmg += w[I_RSEMI]; xeg += w[I_RSEMI + 1]; }
        }
        if ((c === WHITE ? r : 7 - r) === 6 && (c === WHITE ? bkr === 7 : wkr === 0)) { xmg += w[I_R7]; xeg += w[I_R7 + 1]; }
      }
      const zone = mz[1];
      if (c === WHITE) { mg += xmg; eg += xeg; if (zone) { attN0++; attU0 += zone * ATT_WEIGHT[t]; } }
      else { mg -= xmg; eg -= xeg; if (zone) { attN1++; attU1 += zone * ATT_WEIGHT[t]; } }
    }

    // безопасность короля
    if (wQ && attN0 >= 2) { const i = I_SAFETY + 2 * (attU0 > 99 ? 99 : attU0); mg += w[i]; eg += w[i + 1]; }
    if (bQ && attN1 >= 2) { const i = I_SAFETY + 2 * (attU1 > 99 ? 99 : attU1); mg -= w[i]; eg -= w[i + 1]; }
    const sh = this.shCnt;
    if (bQ || bR > 1) {
      this._shield(WHITE, wkf, wkr);
      mg += sh[0] * w[I_SHADV] + sh[1] * w[I_SHMISS] + sh[2] * w[I_SHOWN] + sh[3] * w[I_SHOPEN] + sh[4] * w[I_KEXP];
      eg += sh[0] * w[I_SHADV + 1] + sh[1] * w[I_SHMISS + 1] + sh[2] * w[I_SHOWN + 1] + sh[3] * w[I_SHOPEN + 1] + sh[4] * w[I_KEXP + 1];
    }
    if (wQ || wR > 1) {
      this._shield(BLACK, bkf, bkr);
      mg -= sh[0] * w[I_SHADV] + sh[1] * w[I_SHMISS] + sh[2] * w[I_SHOWN] + sh[3] * w[I_SHOPEN] + sh[4] * w[I_KEXP];
      eg -= sh[0] * w[I_SHADV + 1] + sh[1] * w[I_SHMISS + 1] + sh[2] * w[I_SHOWN + 1] + sh[3] * w[I_SHOPEN + 1] + sh[4] * w[I_KEXP + 1];
    }
    // право хода
    if (this.side === WHITE) { mg += w[I_TEMPO]; eg += w[I_TEMPO + 1]; } else { mg -= w[I_TEMPO]; eg -= w[I_TEMPO + 1]; }

    let phase = this.phase; if (phase > 24) phase = 24;
    let score = ((mg * phase + eg * (24 - phase)) / 24) | 0;

    // эндшпильные поправки
    const wNpm = 3 * (wN + wB) + 5 * wR + 9 * wQ, bNpm = 3 * (bN + bB) + 5 * bR + 9 * bQ;
    if (score > 0) {
      if (wP === 0) {
        if (wNpm <= 3) score >>= 4;
        else if (wN === 2 && wNpm === 6 && bNpm === 0) score >>= 3;
        else if (wNpm - bNpm <= 3) score >>= 2;
      }
      if (bP === 0 && wNpm >= bNpm + 5 && bNpm <= 3) score += mopUp(wk, bk);
    } else if (score < 0) {
      if (bP === 0) {
        if (bNpm <= 3) score = -((-score) >> 4);
        else if (bN === 2 && bNpm === 6 && wNpm === 0) score = -((-score) >> 3);
        else if (bNpm - wNpm <= 3) score = -((-score) >> 2);
      }
      if (wP === 0 && bNpm >= wNpm + 5 && wNpm <= 3) score -= mopUp(bk, wk);
    }
    if (wB === 1 && bB === 1 && wN + wR + wQ + bN + bR + bQ === 0 && wBishopCol !== bBishopCol)
      score = (score * 5) >> 3;

    return this.side === WHITE ? score : -score;
  }

  // Та же оценка, разложенная по термам: для обучения (tools/tune.js).
  // terms: Map(индекс терма → коэффициент «белые минус чёрные»), оценка = Σ k·(W_mg·ф + W_eg·(24−ф))/24.
  evalTrace() {
    const b = this.board, cnt = this.count;
    const terms = new Map();
    const add = (i, v) => { if (v) terms.set(i, (terms.get(i) || 0) + v); };
    for (let sq = 0; sq < 120; sq++) {
      if (sq & 0x88) { sq += 7; continue; }
      const p = b[sq];
      if (!p) continue;
      const t = p & 7, c = p >> 3, s64 = (sq >> 4) * 8 + (sq & 7), sg = c === WHITE ? 1 : -1;
      if (t <= 5) add(TI.MAT + t - 1, sg);
      add(TI.PST + (t - 1) * 64 + (c === WHITE ? s64 : s64 ^ 56), sg);
    }
    if (cnt[3] >= 2) add(TI.BPAIR, 1);
    if (cnt[11] >= 2) add(TI.BPAIR, -1);
    this._pawnScan();
    const pa0 = this.pa[0], pa1 = this.pa[1], wf = this.wf, bf = this.bf, wMin = this.wMin, bMax = this.bMax;
    const wk = this.kingSq[0], bk = this.kingSq[1];
    const wkf = wk & 7, wkr = wk >> 4, bkf = bk & 7, bkr = bk >> 4;
    let attU0 = 0, attN0 = 0, attU1 = 0, attN1 = 0;
    const mz = this.mobZone;
    for (let sq = 0; sq < 120; sq++) {
      if (sq & 0x88) { sq += 7; continue; }
      const p = b[sq];
      if (!p) continue;
      const t = p & 7, c = p >> 3, f = sq & 7, r = sq >> 4;
      if (t === PAWN) {
        if (c === WHITE) {
          if (wf[f] > 1) add(TI.DOUBLED, 1);
          if ((f === 0 || wf[f - 1] === 0) && (f === 7 || wf[f + 1] === 0)) add(TI.ISOLATED, 1);
          if (pa0[sq]) add(TI.PROTECTED, 1);
          if ((f === 0 || bMax[f - 1] <= r) && bMax[f] <= r && (f === 7 || bMax[f + 1] <= r)) {
            const a = sq + 16;
            add(TI.PASSED + r, 1); add(TI.PASSED_KD + r, 2 * sqDist(a, bk) - sqDist(a, wk));
            if (b[a]) add(TI.PASSED_BLOCK + r, 1);
          }
        } else {
          if (bf[f] > 1) add(TI.DOUBLED, -1);
          if ((f === 0 || bf[f - 1] === 0) && (f === 7 || bf[f + 1] === 0)) add(TI.ISOLATED, -1);
          if (pa1[sq]) add(TI.PROTECTED, -1);
          if ((f === 0 || wMin[f - 1] >= r) && wMin[f] >= r && (f === 7 || wMin[f + 1] >= r)) {
            const a = sq - 16, rr = 7 - r;
            add(TI.PASSED + rr, -1); add(TI.PASSED_KD + rr, -(2 * sqDist(a, wk) - sqDist(a, bk)));
            if (b[a]) add(TI.PASSED_BLOCK + rr, -1);
          }
        }
        continue;
      }
      if (t === KING) continue;
      this._mobility(sq, t, c);
      const sg = c === WHITE ? 1 : -1;
      add(MOB_OFF[t] + mz[0], sg);
      if (t === ROOK) {
        const own = c === WHITE ? wf : bf, opp = c === WHITE ? bf : wf;
        if (own[f] === 0) add(opp[f] === 0 ? TI.ROOK_OPEN : TI.ROOK_SEMI, sg);
        if ((c === WHITE ? r : 7 - r) === 6 && (c === WHITE ? bkr === 7 : wkr === 0)) add(TI.ROOK_7TH, sg);
      }
      if (mz[1]) {
        if (c === WHITE) { attN0++; attU0 += mz[1] * ATT_WEIGHT[t]; } else { attN1++; attU1 += mz[1] * ATT_WEIGHT[t]; }
      }
    }
    if (cnt[5] && attN0 >= 2) add(TI.SAFETY + (attU0 > 99 ? 99 : attU0), 1);
    if (cnt[13] && attN1 >= 2) add(TI.SAFETY + (attU1 > 99 ? 99 : attU1), -1);
    const sh = this.shCnt;
    const shAdd = (sg) => { add(TI.SHIELD_ADV, sg * sh[0]); add(TI.SHIELD_MISS, sg * sh[1]); add(TI.SHIELD_OWNOPEN, sg * sh[2]); add(TI.SHIELD_OPEN, sg * sh[3]); add(TI.KING_EXPOSED, sg * sh[4]); };
    if (cnt[13] || cnt[12] > 1) { this._shield(WHITE, wkf, wkr); shAdd(1); }
    if (cnt[5] || cnt[4] > 1) { this._shield(BLACK, bkf, bkr); shAdd(-1); }
    add(TI.TEMPO, this.side === WHITE ? 1 : -1);
    return { terms, phase: Math.min(this.phase, 24), special: this._isSpecialEnding() };
  }

  // Static Exchange Evaluation: материальный итог размена на поле хода
  see(m) {
    const flag = (m >> 17) & 7;
    if (flag === F_EP) return 0;
    const b = this.board;
    const from = m & 127, to = (m >> 7) & 127;
    const gain = this.seeGain, rs = this.seeSq, rp = this.seeP;
    let nrem = 0, d = 0;
    gain[0] = SEE_VAL[b[to] & 7];
    let aType = b[from] & 7, aSq = from;
    let side = this.side;
    while (true) {
      d++;
      gain[d] = SEE_VAL[aType] - gain[d - 1];
      if (Math.max(-gain[d - 1], gain[d]) < 0) break;
      rs[nrem] = aSq; rp[nrem] = b[aSq]; nrem++; b[aSq] = 0;
      side ^= 1;
      aSq = this._lva(to, side);
      if (aSq < 0) break;
      aType = b[aSq] & 7;
      if (aType === KING && this._lva(to, side ^ 1) >= 0) break;
      if (d >= 38) break;
    }
    while (--d) gain[d - 1] = -Math.max(-gain[d - 1], gain[d]);
    for (let i = nrem - 1; i >= 0; i--) b[rs[i]] = rp[i];
    return gain[0];
  }
  _lva(sq, side) {
    const b = this.board, base = side << 3;
    let s;
    if (side === WHITE) {
      s = sq - 15; if (!(s & 0x88) && b[s] === 1) return s;
      s = sq - 17; if (!(s & 0x88) && b[s] === 1) return s;
    } else {
      s = sq + 15; if (!(s & 0x88) && b[s] === 9) return s;
      s = sq + 17; if (!(s & 0x88) && b[s] === 9) return s;
    }
    const N = base | KNIGHT;
    for (let i = 0; i < 8; i++) { s = sq + KNIGHT_OFF[i]; if (!(s & 0x88) && b[s] === N) return s; }
    let best = -1, bestT = 9;
    for (let i = 0; i < 8; i++) {
      const d = i < 4 ? DIAG[i] : ORTHO[i - 4];
      s = sq + d;
      while (!(s & 0x88)) {
        const p = b[s];
        if (p) {
          if ((p >> 3) === side) {
            const t = p & 7;
            const ok = t === QUEEN || (i < 4 ? t === BISHOP : t === ROOK);
            if (ok && t < bestT) { best = s; bestT = t; }
          }
          break;
        }
        s += d;
      }
    }
    if (best >= 0) return best;
    const K = base | KING;
    for (let i = 0; i < 8; i++) { s = sq + KING_OFF[i]; if (!(s & 0x88) && b[s] === K) return s; }
    return -1;
  }

  perft(depth) {
    if (depth === 0) return 1;
    const buf = new Int32Array(256);
    const n = this.genMoves(buf, 0, true);
    let total = 0;
    for (let i = 0; i < n; i++) {
      if (!this.make(buf[i])) continue;
      total += depth === 1 ? 1 : this.perft(depth - 1);
      this.unmake();
    }
    return total;
  }
}

function mopUp(winK, loseK) {
  const lf = loseK & 7, lr = loseK >> 4;
  const cmd = Math.max(3 - lf, lf - 4) + Math.max(3 - lr, lr - 4);
  const md = Math.abs((winK & 7) - lf) + Math.abs((winK >> 4) - lr);
  return 10 * cmd + 4 * (14 - md);
}

// ============================================================== Таблица транспозиций
class TransTable {
  constructor(mb) { this.resize(mb || 16); }
  resize(mb) {
    // 16 байт на запись
    let bits = 10;
    while ((1 << (bits + 1)) * 16 <= mb * 1024 * 1024 && bits < 26) bits++;
    this.size = 1 << bits; this.mask = this.size - 1;
    this.key = new Int32Array(this.size);
    this.move = new Int32Array(this.size);
    this.score = new Int16Array(this.size);
    this.ev = new Int16Array(this.size);
    this.depth = new Int8Array(this.size);
    this.flag = new Uint8Array(this.size);
    this.age = new Uint8Array(this.size);
    this.curAge = 0;
  }
  clear() {
    this.key.fill(0); this.move.fill(0); this.score.fill(0); this.ev.fill(0);
    this.depth.fill(0); this.flag.fill(0); this.age.fill(0); this.curAge = 0;
  }
  newSearch() { this.curAge = (this.curAge + 1) & 255; }
  probe(lo, hi) {
    const i = lo & this.mask;
    return (this.flag[i] && this.key[i] === hi) ? i : -1;
  }
  store(lo, hi, depth, flag, score, ev, move) {
    const i = lo & this.mask;
    if (this.flag[i] && this.key[i] === hi) {
      if (!move) move = this.move[i];
      if (flag !== TT_EXACT && depth < this.depth[i] - 2 && this.age[i] === this.curAge) return;
    } else if (this.flag[i] && this.age[i] === this.curAge && depth < this.depth[i] - 3 && flag !== TT_EXACT) {
      return;
    }
    this.key[i] = hi; this.move[i] = move; this.score[i] = score; this.ev[i] = ev;
    this.depth[i] = depth; this.flag[i] = flag; this.age[i] = this.curAge;
  }
  hashfull() {
    let n = 0;
    for (let i = 0; i < 1000; i++) if (this.flag[i] && this.age[i] === this.curAge) n++;
    return n;
  }
}

// ============================================================== Поиск
const LMR = [];
for (let d = 0; d < 64; d++) {
  LMR.push(new Int8Array(64));
  for (let m = 1; m < 64; m++) LMR[d][m] = d && m ? Math.floor(0.75 + Math.log(d) * Math.log(m) / 2.25) : 0;
}
const LMP = [[0, 3, 4, 6, 9, 13, 18, 24, 31], [0, 5, 7, 10, 15, 21, 28, 37, 47]];

// Поиск на JavaScript: запасной (без WebAssembly) и для ручной оценки (UseNNUE false).
class JsSearcher {
  constructor(opts) {
    opts = opts || {};
    this.pos = new Position();
    this.useNN = opts.nn !== false;
    this.tt = new TransTable(opts.hashMB || 16);
    this.history = new Int32Array(2 * 128 * 128);
    this.killers = new Int32Array(MAX_PLY * 2 + 4);
    this.counter = new Int32Array(16 * 128);
    // история продолжений: насколько хорош ход (фигура, поле) после предыдущего хода (фигура, поле)
    this.cont = new Int32Array(768 * 768);
    // то же через ход: насколько хорош ход после своего предыдущего хода
    this.cont2 = new Int32Array(768 * 768);
    // история взятий: (фигура, поле, кого бьём) — уточняет порядок взятий внутри MVV-LVA
    this.capHist = new Int32Array(16 * 1024);
    this.capBuf = new Int32Array((MAX_PLY + 2) * 32);
    // поправка статической оценки по пешечной структуре: насколько поиск обычно расходится с оценкой
    this.corr = new Int32Array(2 * 16384);
    this.rawStack = new Int32Array(MAX_PLY + 4);
    this.moveBuf = new Int32Array((MAX_PLY + 2) * 256);
    this.scoreBuf = new Int32Array((MAX_PLY + 2) * 256);
    this.quietBuf = new Int32Array((MAX_PLY + 2) * 64);
    this.evalStack = new Int32Array(MAX_PLY + 4);
    this.moveStack = new Int32Array(MAX_PLY + 4);
    this.pieceStack = new Int32Array(MAX_PLY + 4);
    this.pv = new Int32Array(MAX_PLY * MAX_PLY);
    this.pvLen = new Int32Array(MAX_PLY + 1);
    this.externalStop = null; // Int32Array на SharedArrayBuffer (Node / изолированный браузер)
    this.nodes = 0; this.stop = false; this.selDepth = 0;
    this.setPosition(START_FEN, []);
  }

  newGame() {
    this.tt.clear(); this.history.fill(0); this.counter.fill(0); this.killers.fill(0); this.cont.fill(0);
    this.cont2.fill(0); this.capHist.fill(0); this.corr.fill(0);
  }

  setPosition(fen, moves) {
    const pos = this.pos;
    pos.nnOn = false; // ходы партии проигрываем без сети, аккумулятор считаем один раз в конце
    try {
      pos.setFen(fen || START_FEN);
      for (const u of moves || []) {
        const m = pos.uciToMove(u);
        if (!m) throw new Error('Illegal move: ' + u);
        pos.make(m);
      }
      this.lastPos = [fen, moves];
    } catch (e) {
      // ошибка в FEN или ходах: возвращаем прошлую позицию, чтобы не искать в испорченной
      pos.accLock = false;
      if (this.lastPos) { const [f, ms] = this.lastPos; this.lastPos = null; this.setPosition(f, ms); this.lastPos = [f, ms]; }
      else { pos.setFen(START_FEN); if (this.useNN) pos.nnInit(); }
      throw e;
    }
    if (this.useNN) pos.nnInit();
  }
  setUseNN(on) {
    on = !!on;
    if (on !== this.useNN) this.tt.clear(); // в таблице лежат оценки другой функции
    this.useNN = on;
    if (this.useNN) this.pos.nnInit(); else this.pos.nnOn = false;
  }

  // ---------------------------------------------------------------- управление
  // limits: { depth, movetime, nodes, multipv, infinite, wtime, btime, winc, binc, movestogo }
  start(limits) {
    limits = limits || {};
    const pos = this.pos;
    this.limits = limits;
    this.nodes = 0; this.stop = false; this.canStop = false; this.selDepth = 0;
    this.startTime = now();
    this.maxDepth = Math.min(limits.depth || 99, MAX_PLY - 10);
    this.nodeLimit = limits.nodes || 0;
    // время
    this.softTime = 0; this.hardTime = 0;
    // время на ход задано точно: думаем почти всё отведённое время (раньше — около 60 %),
    // запас 8 мс на проверку часов и передачу хода
    if (limits.movetime) { this.hardTime = Math.max(5, limits.movetime - 8); this.softTime = limits.movetime * 0.95; }
    else if (limits.wtime !== undefined || limits.btime !== undefined) {
      const left = (pos.side === WHITE ? limits.wtime : limits.btime) || 0;
      const inc = (pos.side === WHITE ? limits.winc : limits.binc) || 0;
      const mtg = limits.movestogo ? Math.min(limits.movestogo, 40) : 30;
      const base = Math.max(10, left / mtg + inc * 0.75 - 30);
      this.softTime = Math.min(base, left * 0.4);
      this.hardTime = Math.max(10, Math.min(base * 3, left * 0.6 - 50));
    }
    if (limits.infinite) { this.softTime = 0; this.hardTime = 0; }
    if (this.externalStop) Atomics.store(this.externalStop, 0, 0);

    this.tt.newSearch();
    for (let i = 0; i < this.history.length; i++) this.history[i] >>= 1;
    this.killers.fill(0);

    // корневые ходы
    this.rootMoves = pos.legalMoves();
    // ходы, которые запрещено рассматривать (searchmoves)
    if (limits.searchmoves && limits.searchmoves.length) {
      const allowed = new Set(limits.searchmoves);
      this.rootMoves = this.rootMoves.filter(m => allowed.has(pos.moveToUci(m)));
    }
    this.multiPV = Math.max(1, Math.min(limits.multipv || 1, this.rootMoves.length || 1));
    this.lines = [];
    this.depthDone = 0;
    const ti = this.tt.probe(pos.hashLo, pos.hashHi);
    if (ti >= 0) {
      const tm = this.tt.move[ti], k = this.rootMoves.indexOf(tm);
      if (k > 0) { this.rootMoves.splice(k, 1); this.rootMoves.unshift(tm); }
    }
    this.bookMove = null;
    if (limits.book && this.rootMoves.length) {
      const bm = pos.bookMoves();
      if (bm) {
        const c = pickBookMove(bm);
        this.bookMove = c;
        this.lines = [{ move: c.m, score: 0, pv: [c.m], depth: 0 }];
        this.finished = true;
        return;
      }
    }
    this.finished = this.rootMoves.length === 0;
    if (this.finished) {
      this.lines = [{ move: 0, score: pos.inCheck() ? -MATE : 0, pv: [], depth: 0 }];
    }
  }

  elapsed() { return now() - this.startTime; }

  checkTime() {
    if (!this.canStop) return;
    if (this.hardTime && this.elapsed() >= this.hardTime) this.stop = true;
    else if (this.nodeLimit && this.nodes >= this.nodeLimit) this.stop = true;
    else if (this.externalStop && Atomics.load(this.externalStop, 0)) this.stop = true;
  }

  // Одна итерация углубления. Возвращает true, если стоит продолжать.
  iterate() {
    if (this.finished || this.stop) return false;
    const depth = this.depthDone + 1;
    if (depth > this.maxDepth) { this.finished = true; return false; }
    const pos = this.pos;
    const excluded = [];
    const newLines = [];
    for (let k = 0; k < this.multiPV; k++) {
      const prev = this.lines[k];
      let alpha = -INF, beta = INF, delta = 18;
      if (depth >= 4 && prev && Math.abs(prev.score) < MATE_BOUND) {
        alpha = Math.max(-INF, prev.score - delta); beta = Math.min(INF, prev.score + delta);
      }
      let res;
      while (true) {
        res = this.rootSearch(depth, alpha, beta, excluded, k);
        if (this.stop) break;
        if (res.score <= alpha) { beta = (alpha + beta) >> 1; alpha = Math.max(-INF, res.score - delta); }
        else if (res.score >= beta) { beta = Math.min(INF, res.score + delta); }
        else break;
        delta += delta >> 1;
        if (delta > 700) { alpha = -INF; beta = INF; }
      }
      if (this.stop) {
        // прерванная итерация: берём ход, если он успел улучшить результат
        if (k === 0 && res && res.reliable && res.move) newLines.push({ move: res.move, score: res.score, pv: res.pv, depth: depth });
        break;
      }
      newLines.push({ move: res.move, score: res.score, pv: res.pv, depth: depth });
      excluded.push(res.move);
      this.canStop = true;
    }
    // слить новые линии со старыми (при прерывании — дополнить прошлой глубиной)
    if (newLines.length) {
      const merged = newLines.slice();
      if (this.stop) for (const l of this.lines) if (!merged.some(x => x.move === l.move)) merged.push(l);
      if (merged.length > this.multiPV) merged.length = this.multiPV;
      merged.sort((a, b) => b.score - a.score);
      this.lines = merged;
      const order = this.lines.map(l => l.move);
      this.rootMoves.sort((a, b) => {
        const ia = order.indexOf(a), ib = order.indexOf(b);
        return (ia < 0 ? 999 : ia) - (ib < 0 ? 999 : ib);
      });
    }
    if (this.stop) { this.finished = true; return false; }
    this.depthDone = depth;
    this.canStop = true;
    const best = this.lines[0];
    // ранняя остановка
    if (this.rootMoves.length === 1 && !this.limits.infinite && !this.limits.depth && depth >= 4) { this.finished = true; return false; }
    if (Math.abs(best.score) >= MATE_BOUND && depth >= (MATE - Math.abs(best.score)) * 2 + 4 && !this.limits.infinite) { this.finished = true; return false; }
    if (this.softTime && this.elapsed() >= this.softTime) { this.finished = true; return false; }
    if (this.nodeLimit && this.nodes >= this.nodeLimit) { this.finished = true; return false; }
    if (depth >= this.maxDepth) { this.finished = true; return false; }
    return true;
  }

  rootSearch(depth, alpha, beta, excluded, pvIdx) {
    const pos = this.pos;
    let best = -INF, bestMove = 0, bestPv = [], reliable = false;
    let searched = 0;
    const alpha0 = alpha;
    this.pvLen[0] = 0;
    for (let i = 0; i < this.rootMoves.length; i++) {
      const m = this.rootMoves[i];
      if (excluded.indexOf(m) >= 0) continue;
      pos.make(m);
      this.moveStack[0] = m; this.pieceStack[0] = pos.board[(m >> 7) & 127];
      let score;
      if (searched === 0) score = -this.search(depth - 1, -beta, -alpha, 1, false);
      else {
        score = -this.search(depth - 1, -alpha - 1, -alpha, 1, true);
        if (score > alpha && score < beta && !this.stop) score = -this.search(depth - 1, -beta, -alpha, 1, false);
      }
      pos.unmake();
      if (this.stop) break;
      searched++;
      if (score > best) {
        best = score; bestMove = m;
        bestPv = [m];
        for (let j = 1; j < this.pvLen[1]; j++) bestPv.push(this.pv[MAX_PLY + j]);
        if (score > alpha) {
          alpha = score;
          if (score > alpha0) reliable = true;
          if (score >= beta) break;
        }
      }
    }
    if (bestMove && pvIdx === 0 && !this.stop) {
      const flag = best >= beta ? TT_LOWER : (best > alpha0 ? TT_EXACT : TT_UPPER);
      this.tt.store(pos.hashLo, pos.hashHi, depth, flag, toTT(best, 0), 0, bestMove);
    }
    return { move: bestMove, score: best, pv: bestPv, reliable };
  }

  search(depth, alpha, beta, ply, cutNode, excl = 0) {
    const pos = this.pos, tt = this.tt;
    const pvNode = beta - alpha > 1;
    this.pvLen[ply] = ply;
    if ((++this.nodes & 255) === 0) this.checkTime();
    if (this.stop) return 0;
    if (ply > this.selDepth) this.selDepth = ply;

    // ничьи
    if (pos.isRepetition() || pos.insufficientMaterial()) return 0;
    // правило 50 ходов, но мат последним ходом важнее
    if (pos.halfmove >= 100 && (!pos.inCheck() || pos.hasLegalMove())) return 0;
    // mate distance pruning
    if (alpha < -MATE + ply) alpha = -MATE + ply;
    if (beta > MATE - ply - 1) beta = MATE - ply - 1;
    if (alpha >= beta) return alpha;
    if (ply >= MAX_PLY - 2) return pos.evaluate();

    const inCheck = pos.inCheck();
    if (inCheck) depth++;
    if (depth <= 0) { this.nodes--; return this.qsearch(alpha, beta, ply); }

    // таблица транспозиций
    let ttMove = 0, ttScore = 0, ttFlag = 0, ttDepth = -1, ttEval = 0;
    const ti = tt.probe(pos.hashLo, pos.hashHi);
    if (ti >= 0) {
      ttMove = tt.move[ti]; ttScore = fromTT(tt.score[ti], ply); ttFlag = tt.flag[ti];
      ttDepth = tt.depth[ti]; ttEval = tt.ev[ti];
      if (!pvNode && !excl && ttDepth >= depth &&
          (ttFlag === TT_EXACT || (ttFlag === TT_LOWER && ttScore >= beta) || (ttFlag === TT_UPPER && ttScore <= alpha))) {
        if (ttMove && ttScore >= beta && !((ttMove >> 20) & 1) && !((ttMove >> 14) & 7)) this.updateQuietStats(ttMove, ply, depth, 0);
        return ttScore;
      }
    }

    let staticEval, rawEval = 0;
    if (inCheck) staticEval = this.evalStack[ply] = (ply >= 2 ? this.evalStack[ply - 2] : 0);
    else {
      rawEval = (ti >= 0 && ttEval !== 0) ? ttEval : pos.evaluate();
      staticEval = this.corrected(rawEval);
      this.evalStack[ply] = staticEval;
      // уточняем оценкой из TT
      if (ti >= 0 && ((ttFlag === TT_LOWER && ttScore > staticEval) || (ttFlag === TT_UPPER && ttScore < staticEval) || ttFlag === TT_EXACT))
        if (Math.abs(ttScore) < MATE_BOUND) staticEval = ttScore;
    }
    this.rawStack[ply] = rawEval;
    const improving = !inCheck && ply >= 2 && this.evalStack[ply] > this.evalStack[ply - 2];

    if (!pvNode && !inCheck && !excl) {
      // reverse futility
      if (depth <= 7 && Math.abs(beta) < MATE_BOUND && staticEval - 75 * (depth - (improving ? 1 : 0)) >= beta)
        return staticEval;
      // razoring
      if (depth <= 3 && staticEval + 200 + 160 * depth <= alpha) {
        const s = this.qsearch(alpha, alpha + 1, ply);
        if (s <= alpha) return s;
      }
      // нулевой ход
      if (depth >= 3 && staticEval >= beta && this.moveStack[ply - 1] !== 0 && pos.hasNonPawn(pos.side) && Math.abs(beta) < MATE_BOUND) {
        const R = 3 + (depth >> 2) + Math.min(3, ((staticEval - beta) / 200) | 0);
        pos.makeNull();
        this.moveStack[ply] = 0; this.pieceStack[ply] = 0;
        const s = -this.search(depth - 1 - R, -beta, -beta + 1, ply + 1, !cutNode);
        pos.unmakeNull();
        if (this.stop) return 0;
        if (s >= beta) {
          if (depth < 10) return s >= MATE_BOUND ? beta : s;
          // проверка при большой глубине
          const v = this.search(depth - R, beta - 1, beta, ply, false);
          if (v >= beta) return s >= MATE_BOUND ? beta : s;
        }
      }
      // ProbCut-lite: опускаем
    }

    // internal iterative reduction
    if (depth >= 4 && !ttMove && (pvNode || cutNode)) depth--;

    // одиночное продление: если все ходы, кроме хода из таблицы, заметно хуже, ход из таблицы
    // «единственный» — считаем его на полуход глубже; если и без него есть отсечение — выходим сразу
    let singExt = 0;
    if (!excl && depth >= 8 && ttMove && ttDepth >= depth - 3 && ttFlag !== TT_UPPER && Math.abs(ttScore) < MATE_BOUND) {
      const sBeta = ttScore - 2 * depth;
      const v = this.search((depth - 1) >> 1, sBeta - 1, sBeta, ply, cutNode, ttMove);
      if (this.stop) return 0;
      if (v < sBeta) singExt = 1;
      else if (sBeta >= beta) return sBeta;
      this.pvLen[ply] = ply;
    }

    const start = ply * 256;
    const end = pos.genMoves(this.moveBuf, start, true);
    this.scoreMoves(start, end, ttMove, ply);

    const moves = this.moveBuf, scores = this.scoreBuf;
    const k1 = this.killers[ply * 2], k2 = this.killers[ply * 2 + 1];
    const prev = this.moveStack[ply - 1];
    const cm = prev ? this.counter[this.pieceStack[ply - 1] * 128 + ((prev >> 7) & 127)] : 0;
    const qbase = ply * 64;
    let best = -INF, bestMove = 0, legal = 0, quiets = 0, caps = 0;
    const alpha0 = alpha, cbase0 = ply * 32;
    const lmpLimit = depth <= 8 ? LMP[improving ? 1 : 0][depth] : 999;

    for (let i = start; i < end; i++) {
      // выбор лучшего оставшегося хода
      let bi = i, bs = scores[i];
      for (let j = i + 1; j < end; j++) if (scores[j] > bs) { bs = scores[j]; bi = j; }
      const m = moves[bi];
      if (bi !== i) { moves[bi] = moves[i]; moves[i] = m; scores[bi] = scores[i]; scores[i] = bs; }
      if (m === excl) continue;

      const isCap = (m >> 20) & 1, promo = (m >> 14) & 7;
      const quiet = !isCap && !promo;
      const canPrune = !pvNode && !inCheck && legal > 0 && best > -MATE_BOUND;

      if (canPrune) {
        if (quiet) {
          if (quiets >= lmpLimit) continue;
          // тихий ход на поле, где фигуру выгодно забрать
          if (depth <= 8 && bs < 7000000 && pos.see(m) < -25 * depth * depth) continue;
        } else if (depth <= 6 && bs < 5000000 && pos.see(m) < -90 * depth) {
          continue;
        }
      }
      if (!pos.make(m, !inCheck)) continue;
      legal++;
      const givesCheck = pos.inCheck();

      if (canPrune && quiet && !givesCheck && depth <= 8 && staticEval + 90 + 85 * depth <= alpha) {
        pos.unmake();
        if (quiets < 64) this.quietBuf[qbase + quiets] = m;
        quiets++;
        continue;
      }

      this.moveStack[ply] = m; this.pieceStack[ply] = pos.board[(m >> 7) & 127];
      const newDepth = depth - 1 + (m === ttMove ? singExt : 0);
      let score;
      if (legal === 1) {
        score = -this.search(newDepth, -beta, -alpha, ply + 1, !pvNode && !cutNode);
      } else {
        let R = 0;
        if (depth >= 3 && quiet && !givesCheck) {
          R = LMR[depth < 64 ? depth : 63][legal < 64 ? legal : 63];
          if (pvNode) R--;
          if (!improving) R++;
          if (cutNode) R++;
          if (m === k1 || m === k2 || m === cm) R -= 2;
          const to = (m >> 7) & 127;
          const cbase = this.prevContBase(ply), cbase2 = this.prevContBase2(ply), key = this.contKey(pos.board[to], to);
          const hv = this.history[((pos.side ^ 1) << 14) | ((m & 127) << 7) | to] +
            (cbase >= 0 ? this.cont[cbase + key] : 0) + (cbase2 >= 0 ? this.cont2[cbase2 + key] : 0);
          R -= (hv / 10000) | 0;
          if (R < 0) R = 0;
          if (R > newDepth - 1) R = newDepth - 1 > 0 ? newDepth - 1 : 0;
        } else if (depth >= 3 && isCap && !givesCheck && !pvNode && bs < 5000000) {
          R = 1;
        }
        score = -this.search(newDepth - R, -alpha - 1, -alpha, ply + 1, true);
        if (score > alpha && R > 0) score = -this.search(newDepth, -alpha - 1, -alpha, ply + 1, !cutNode);
        if (score > alpha && score < beta) score = -this.search(newDepth, -beta, -alpha, ply + 1, false);
      }
      pos.unmake();
      if (this.stop) return 0;

      if (score > best) {
        best = score;
        if (score > alpha) {
          alpha = score; bestMove = m;
          // PV
          const base = ply * MAX_PLY;
          this.pv[base + ply] = m;
          const cl = this.pvLen[ply + 1];
          for (let j = ply + 1; j < cl; j++) this.pv[base + j] = this.pv[base + MAX_PLY + j];
          this.pvLen[ply] = cl > ply + 1 ? cl : ply + 1;
          if (score >= beta) {
            if (quiet) this.updateQuietStats(m, ply, depth, quiets);
            this.updateCaptureStats(quiet ? 0 : m, ply, depth, caps);
            break;
          }
        }
      }
      if (quiet) { if (quiets < 64) this.quietBuf[qbase + quiets] = m; quiets++; }
      else if (isCap) { if (caps < 32) this.capBuf[cbase0 + caps] = m; caps++; }
    }

    if (legal === 0) return excl ? alpha : inCheck ? -MATE + ply : 0;
    if (excl) return best;

    const flag = best >= beta ? TT_LOWER : (best > alpha0 ? TT_EXACT : TT_UPPER);
    if (!inCheck && Math.abs(best) < MATE_BOUND && !(bestMove && (((bestMove >> 20) & 1) || ((bestMove >> 14) & 7)))) {
      const ev = this.evalStack[ply];
      if (!(flag === TT_LOWER && best <= ev) && !(flag === TT_UPPER && best >= ev)) this.updateCorrection(best - ev, depth);
    }
    tt.store(pos.hashLo, pos.hashHi, depth, flag, toTT(best, ply), inCheck ? 0 : this.rawStack[ply], bestMove);
    return best;
  }

  // поправка оценки по пешечной структуре — в 1/16 сантипешки, до ±256 пешечных сотых
  corrected(raw) {
    const pos = this.pos;
    const v = raw + (this.corr[(pos.side << 14) | (pos.pawnKey & 16383)] >> 4);
    return v > 20000 ? 20000 : v < -20000 ? -20000 : v;
  }
  updateCorrection(diff, depth) {
    const pos = this.pos, idx = (pos.side << 14) | (pos.pawnKey & 16383);
    if (diff > 512) diff = 512; else if (diff < -512) diff = -512;
    // скользящее среднее: поправка сдвигается к нужной на долю w/256 (не больше 1/16 за раз)
    const w = depth + 1 < 16 ? depth + 1 : 16;
    let e = this.corr[idx] + ((diff * w / 16) | 0);
    if (e > 4096) e = 4096; else if (e < -4096) e = -4096;
    this.corr[idx] = e;
  }

  capKey(m) {
    const b = this.pos.board, to = (m >> 7) & 127;
    const victim = ((m >> 17) & 7) === F_EP ? PAWN : (b[to] & 7);
    return (b[m & 127] << 10) | (to << 3) | victim;
  }
  // отсечение взятием — плюс этому взятию; любое отсечение — минус взятиям, которые не помогли
  updateCaptureStats(m, ply, depth, caps) {
    const bonus = Math.min(depth * depth * 16, 1600), h = this.capHist;
    if (m) { const i = this.capKey(m); h[i] += bonus - ((h[i] * bonus) >> 14); }
    const n = Math.min(caps, 32), base = ply * 32;
    for (let k = 0; k < n; k++) {
      const q = this.capBuf[base + k];
      if (q === m) continue;
      const j = this.capKey(q);
      h[j] -= bonus + ((h[j] * bonus) >> 14);
    }
  }

  // индекс (фигура, поле) для истории продолжений: 12 фигур x 64 поля
  contKey(p, sq) { return (((p >> 3) * 6 + (p & 7) - 1) << 6) | ((sq >> 4) << 3) | (sq & 7); }
  prevContBase(ply) {
    if (ply < 1) return -1;
    const prev = this.moveStack[ply - 1];
    if (!prev) return -1;
    return this.contKey(this.pieceStack[ply - 1], (prev >> 7) & 127) * 768;
  }
  prevContBase2(ply) {
    if (ply < 2) return -1;
    const prev = this.moveStack[ply - 2];
    if (!prev) return -1;
    return this.contKey(this.pieceStack[ply - 2], (prev >> 7) & 127) * 768;
  }

  updateQuietStats(m, ply, depth, quiets) {
    const pos = this.pos, side = pos.side;
    const k = ply * 2;
    if (this.killers[k] !== m) { this.killers[k + 1] = this.killers[k]; this.killers[k] = m; }
    const bonus = Math.min(depth * depth * 16, 1600);
    const h = this.history;
    const idx = (side << 14) | ((m & 127) << 7) | ((m >> 7) & 127);
    h[idx] += bonus - ((h[idx] * bonus) >> 14);
    const n = Math.min(quiets, 64), qbase = ply * 64;
    for (let i = 0; i < n; i++) {
      const q = this.quietBuf[qbase + i];
      if (q === m) continue;
      const j = (side << 14) | ((q & 127) << 7) | ((q >> 7) & 127);
      h[j] -= bonus + ((h[j] * bonus) >> 14);
    }
    const cb = this.prevContBase(ply);
    if (cb >= 0) {
      const ch = this.cont, b = pos.board;
      const ci = cb + this.contKey(b[m & 127], (m >> 7) & 127);
      ch[ci] += bonus - ((ch[ci] * bonus) >> 14);
      for (let i = 0; i < n; i++) {
        const q = this.quietBuf[qbase + i];
        if (q === m) continue;
        const cj = cb + this.contKey(b[q & 127], (q >> 7) & 127);
        ch[cj] -= bonus + ((ch[cj] * bonus) >> 14);
      }
    }
    const cb2 = this.prevContBase2(ply);
    if (cb2 >= 0) {
      const ch = this.cont2, b = pos.board;
      const ci = cb2 + this.contKey(b[m & 127], (m >> 7) & 127);
      ch[ci] += bonus - ((ch[ci] * bonus) >> 14);
      for (let i = 0; i < n; i++) {
        const q = this.quietBuf[qbase + i];
        if (q === m) continue;
        const cj = cb2 + this.contKey(b[q & 127], (q >> 7) & 127);
        ch[cj] -= bonus + ((ch[cj] * bonus) >> 14);
      }
    }
    const prev = this.moveStack[ply - 1];
    if (ply > 0 && prev) this.counter[this.pieceStack[ply - 1] * 128 + ((prev >> 7) & 127)] = m;
  }

  scoreMoves(start, end, ttMove, ply) {
    const pos = this.pos, b = pos.board, side = pos.side;
    const k1 = this.killers[ply * 2], k2 = this.killers[ply * 2 + 1];
    const prev = ply > 0 ? this.moveStack[ply - 1] : 0;
    const cm = prev ? this.counter[this.pieceStack[ply - 1] * 128 + ((prev >> 7) & 127)] : 0;
    const moves = this.moveBuf, scores = this.scoreBuf, h = this.history;
    const cb = this.prevContBase(ply), ch = this.cont;
    const cb2 = this.prevContBase2(ply), ch2 = this.cont2, chist = this.capHist;
    for (let i = start; i < end; i++) {
      const m = moves[i];
      if (m === ttMove) { scores[i] = 30000000; continue; }
      const from = m & 127, to = (m >> 7) & 127, promo = (m >> 14) & 7;
      if ((m >> 20) & 1) {
        const victim = ((m >> 17) & 7) === F_EP ? PAWN : (b[to] & 7);
        const attacker = b[from] & 7;
        let s = SEE_VAL[victim] * 16 - attacker + (chist[(b[from] << 10) | (to << 3) | victim] >> 5);
        if (promo === QUEEN) s += 8000;
        // потенциально проигрышные взятия — проверяем SEE
        if (SEE_VAL[attacker] > SEE_VAL[victim] && pos.see(m) < 0) scores[i] = -2000000 + s;
        else scores[i] = 10000000 + s;
      } else if (promo) {
        scores[i] = promo === QUEEN ? 9500000 : -3000000 + promo;
      } else if (m === k1) scores[i] = 9000000;
      else if (m === k2) scores[i] = 8000000;
      else if (m === cm) scores[i] = 7000000;
      else {
        const key = this.contKey(b[from], to);
        scores[i] = h[(side << 14) | (from << 7) | to] + (cb >= 0 ? ch[cb + key] : 0) + (cb2 >= 0 ? ch2[cb2 + key] : 0);
      }
    }
  }

  qsearch(alpha, beta, ply) {
    const pos = this.pos, tt = this.tt;
    this.pvLen[ply] = ply;
    if ((++this.nodes & 255) === 0) this.checkTime();
    if (this.stop) return 0;
    if (ply > this.selDepth) this.selDepth = ply;
    if (ply >= MAX_PLY - 2) return pos.evaluate();
    if (pos.insufficientMaterial()) return 0;

    const pvNode = beta - alpha > 1;
    const ti = tt.probe(pos.hashLo, pos.hashHi);
    let ttMove = 0, ev = 0, haveEv = false;
    if (ti >= 0) {
      const s = fromTT(tt.score[ti], ply), f = tt.flag[ti];
      if (!pvNode && (f === TT_EXACT || (f === TT_LOWER && s >= beta) || (f === TT_UPPER && s <= alpha))) return s;
      ttMove = tt.move[ti];
      ev = tt.ev[ti]; haveEv = ev !== 0;
    }

    const inCheck = pos.inCheck();
    let best, standPat = 0, raw = 0;
    if (inCheck) best = -INF;
    else {
      raw = haveEv ? ev : pos.evaluate();
      standPat = this.corrected(raw);
      if (standPat >= beta) return standPat;
      if (standPat > alpha) alpha = standPat;
      best = standPat;
    }
    const start = ply * 256;
    const end = pos.genMoves(this.moveBuf, start, inCheck);
    // сортировка: MVV-LVA
    const moves = this.moveBuf, scores = this.scoreBuf, b = pos.board;
    if (inCheck) this.scoreMoves(start, end, ttMove, ply);
    else {
      for (let i = start; i < end; i++) {
        const m = moves[i];
        const victim = ((m >> 17) & 7) === F_EP ? PAWN : (b[(m >> 7) & 127] & 7);
        scores[i] = m === ttMove ? 1e7 : SEE_VAL[victim] * 16 - (b[m & 127] & 7) + (((m >> 14) & 7) === QUEEN ? 8000 : 0);
      }
    }
    let legal = 0, bestMove = 0;
    const alpha0 = alpha;
    for (let i = start; i < end; i++) {
      let bi = i, bs = scores[i];
      for (let j = i + 1; j < end; j++) if (scores[j] > bs) { bs = scores[j]; bi = j; }
      const m = moves[bi];
      if (bi !== i) { moves[bi] = moves[i]; moves[i] = m; scores[bi] = scores[i]; scores[i] = bs; }
      if (!inCheck) {
        const promo = (m >> 14) & 7;
        const victim = ((m >> 17) & 7) === F_EP ? PAWN : (b[(m >> 7) & 127] & 7);
        if (!promo && standPat + SEE_VAL[victim] + 180 <= alpha) continue;
        if (SEE_VAL[b[m & 127] & 7] > SEE_VAL[victim] && pos.see(m) < 0) continue;
      }
      if (!pos.make(m, !inCheck)) continue;
      legal++;
      const score = -this.qsearch(-beta, -alpha, ply + 1);
      pos.unmake();
      if (this.stop) return 0;
      if (score > best) {
        best = score;
        if (score > alpha) {
          alpha = score; bestMove = m;
          const base = ply * MAX_PLY;
          this.pv[base + ply] = m;
          const cl = this.pvLen[ply + 1];
          for (let j = ply + 1; j < cl; j++) this.pv[base + j] = this.pv[base + MAX_PLY + j];
          this.pvLen[ply] = cl > ply + 1 ? cl : ply + 1;
          if (score >= beta) break;
        }
      }
    }
    if (inCheck && legal === 0) return -MATE + ply;
    const flag = best >= beta ? TT_LOWER : (best > alpha0 ? TT_EXACT : TT_UPPER);
    tt.store(pos.hashLo, pos.hashHi, 0, flag, toTT(best, ply), inCheck ? 0 : raw, bestMove);
    return best;
  }

  // ---------------------------------------------------------------- результат
  info() {
    const pos = this.pos;
    const t = Math.max(1, this.elapsed());
    return {
      depth: this.depthDone || (this.lines[0] ? this.lines[0].depth : 0),
      seldepth: this.selDepth,
      nodes: this.nodes,
      time: Math.round(t),
      nps: Math.round(this.nodes * 1000 / t),
      hashfull: this.tt.hashfull(),
      book: this.bookMove ? { n: this.bookMove.n, score: this.bookMove.score } : null,
      lines: this.lines.map(l => ({
        move: pos.moveToUci(l.move),
        score: l.score,
        cp: Math.abs(l.score) < MATE_BOUND ? l.score : null,
        mate: Math.abs(l.score) >= MATE_BOUND ? (l.score > 0 ? Math.ceil((MATE - l.score) / 2) : -Math.ceil((MATE + l.score) / 2)) : null,
        pv: l.pv.map(m => uciOfMove(m)),
        depth: l.depth,
      })),
    };
  }

  // Полный синхронный поиск (Node / тесты)
  run(limits, onInfo) {
    this.start(limits);
    while (this.iterate()) { if (onInfo) onInfo(this.info()); }
    const inf = this.info();
    if (onInfo) onInfo(inf);
    return inf;
  }
}

function toTT(s, ply) { return s >= MATE_BOUND ? s + ply : s <= -MATE_BOUND ? s - ply : s; }
function fromTT(s, ply) { return s >= MATE_BOUND ? s - ply : s <= -MATE_BOUND ? s + ply : s; }
function uciOfMove(m) {
  const promo = (m >> 14) & 7;
  return sqName(m & 127) + sqName((m >> 7) & 127) + (promo ? ' pnbrqk'[promo] : '');
}

// ============================================================== Ядро поиска на WebAssembly
// core/blizzard.c: битборды, легальная генерация ходов, сеть на SIMD и тот же поиск, что в JsSearcher, —
// в несколько раз быстрее. Собирается командой node core/build.js и вписывается сюда между метками.
const CORE_WASM_B64 = /*CORE_WASM*/'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QQApA8iNhIAAQQApA4iQhIAAg0IAUg0AIAZBACkD2OylgACDQgBSDQAgCEEAKQPY6KOAAINCAFINAEEAKALEwNqAAEEAKQPYwtqAACATg0KAiJLAgIKkDH5BADUCxMbagACIp2pBA3RBsPjXgABqKQMAIBuDQgBSDQBBACgCxPDXgABBACkD2PLXgAAgE4NCgIiggJDAgICBf35BADUCxPbXgACIp2pBA3RBsPClgABqKQMAIByDQgBSDQBBBiAPIBMQioCAgAANACAAIAJBAnRqQYSDBjYCACACQQFqIQILIBNCDoNCAFINAiAFQQJxRQ0CQQApA8iNhIAAQQApA/iPhIAAg0IAUg0CIAZBACkDyOylgACDQgBSDQIgCEEAKQPI6KOAAINCAFINAkEAKAK8wNqAAEEAKQPIwtqAACATg0KIiICA0sCGlAh+QQA1ArzG2oAAiKdqQQN0QbD414AAaikDACAbg0IAUg0CQQAoArzw14AAQQApA8jy14AAIBODQoCJgMCAgITACH5BADUCvPbXgACIp2pBA3RBsPClgABqKQMAIByDQgBSDQJBAiAPIBMQioCAgAANAkGEgQYhBQwBCwJAIBNCgICAgICAgIDgAINCAFINACAFQQRxRQ0AIBBBA3QiDEGIjYSAAGopAwAiCiADQQl0QciThIAAaikDAINCAFINACAMQZCNhIAAaikDACILQQApA5jwpYAAg0IAUg0AIBBBA3RBsI2EgABqKQMAIh5BACkDmOyjgACDQgBSDQBBACgCpMLagABBACkDmMbagAAgE4NCgILAmYCCooACfkEANQKkyNqAAIinakEDdEGw+NeAAGopAwAgG4NCAFINAEEAKAKk8teAAEEAKQOY9teAACATg0KHgLDCoIDAgDB+QQA1AqT414AAiKdqQQN0QbDwpYAAaikDACAcg0IAUg0AIANBCXRB0JOEgABqKQMAIAqDQgBSDQAgC0EAKQOg8KWAAINCAFINACAeQQApA6Dso4AAg0IAUg0AQQAoAqjC2oAAQQApA6DG2oAAIBODQoCCkJSggJCgAX5BADUCqMjagACIp2pBA3RBsPjXgABqKQMAIBuDQgBSDQBBACgCqPLXgABBACkDoPbXgAAgE4NChOCEhIDDiMQIfkEANQKo+NeAAIinakEDdEGw8KWAAGopAwAgHINCAFIN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'/*END*/;
let CORE_MOD, CORE_ON = true;
function coreModule() {
  if (CORE_MOD !== undefined) return CORE_MOD;
  CORE_MOD = null;
  try {
    if (typeof WebAssembly === 'object' && CORE_WASM_B64) CORE_MOD = new WebAssembly.Module(b64bytes(CORE_WASM_B64));
  } catch (e) { CORE_MOD = null; }
  return CORE_MOD;
}
function setCore(on) { CORE_ON = !!on; }
const sq64 = (s) => ((s >> 4) << 3) | (s & 7);
// параметры поиска ядра — в том же порядке, что enum в core/blizzard.c (подбираются tools/spsa.js)
const CORE_PARAMS = ['RFP_MARGIN', 'RFP_DEPTH', 'RAZOR_BASE', 'RAZOR_MUL', 'NMP_BASE', 'NMP_DIV', 'FUT_BASE', 'FUT_MUL',
  'SEEQ_MUL', 'SEEC_MUL', 'LMR_BASE', 'LMR_DIV', 'LMR_HIST', 'SE_DEPTH', 'SE_MUL', 'QS_DELTA', 'ASP_DELTA', 'HIST_MUL',
  'HIST_MAX', 'PROBCUT', 'HISTP', 'SE_DOUBLE', 'SE_NEG', 'LMP_MUL', 'CORR_NP', 'TTCAP', 'CUTCNT', 'DEEPER', 'PRIOR', 'TM',
  'TTPV', 'CHKRED', 'CONT4', 'CCORR', 'QSTT', 'DRAW', 'FHBLEND', 'SMPSKIP', 'NMPD', 'CUTRED', 'CAPLMR', 'NMPTT', 'RFPRET'];

class CoreSearcher {
  constructor(opts) {
    opts = opts || {};
    this.useNN = true;
    this.hashMB = opts.hashMB || 16;
    this.externalStop = null;
    this._stop = false;
    const self = this;
    this.inst = new WebAssembly.Instance(CORE_MOD, { env: { now, stop: () => (self.externalStop && Atomics.load(self.externalStop, 0) ? 1 : 0) } });
    const W = this.W = this.inst.exports;
    W.init();
    const n = NN;
    if (!W.nn_alloc(n.H, n.NB, n.KB)) throw new Error('core: no memory for the network');
    new Int16Array(W.memory.buffer, W.nn_w1(), n.NI * n.H).set(n.W1);
    new Int16Array(W.memory.buffer, W.nn_b1(), n.H).set(n.b1);
    new Float32Array(W.memory.buffer, W.nn_w2(), n.NB * 2 * n.H).set(n.W2);
    new Float32Array(W.memory.buffer, W.nn_b2(), n.NB).set(n.b2);
    W.nn_ready(n.qa, n.outScale);
    W.tt_resize(this.hashMB);
    W.nn_enable(1);
    this.js = null; // поиск на JavaScript — только для ручной оценки
    this.tt = {
      resize: (mb) => { self.hashMB = mb; self.W.tt_resize(mb); if (self.js) self.js.tt.resize(mb); },
      clear: () => { self.W.new_game(); },
      hashfull: () => self.W.hashfull(),
    };
    this.pos = new Position();
    this.lines = []; this.finished = true; this.bookMove = null; this.startTime = now();
    this.setPosition(START_FEN, []);
  }
  get stop() { return this.js && !this.useNN ? this.js.stop : this._stop; }
  set stop(v) { this._stop = !!v; this.W.set_stop(v ? 1 : 0); if (this.js) this.js.stop = !!v; }
  _io() { return new Int32Array(this.W.memory.buffer, this.W.io(), 4096); }
  _sendPosition(fen, moves) {
    const p0 = new Position(); p0.setFen(fen || START_FEN);
    const io = this._io();
    for (let s = 0; s < 64; s++) io[s] = p0.board[((s >> 3) << 4) | (s & 7)];
    this.W.set_position(p0.side, p0.castle, p0.ep >= 0 ? sq64(p0.ep) : -1, p0.halfmove);
    for (const u of moves || []) {
      const m = p0.uciToMove(u);
      if (!m || !this.W.play(sq64(m & 127), sq64((m >> 7) & 127), (m >> 14) & 7)) throw new Error('Illegal move: ' + u);
      p0.make(m);
    }
    this.W.sync();
  }
  newGame() { this.W.new_game(); if (this.js) this.js.newGame(); }
  // параметр поиска ядра по имени (CORE_PARAMS); false — нет такого
  setParam(name, v) { const i = CORE_PARAMS.indexOf(name); if (i < 0) return false; this.W.set_param(i, v | 0); return true; }
  getParams() { return Object.fromEntries(CORE_PARAMS.map((n, i) => [n, this.W.get_param(i)])); }
  setPosition(fen, moves) {
    const pos = this.pos;
    pos.nnOn = false;
    try {
      pos.setFen(fen || START_FEN);
      for (const u of moves || []) {
        const m = pos.uciToMove(u);
        if (!m) throw new Error('Illegal move: ' + u);
        pos.make(m);
      }
      this._sendPosition(fen, moves);
      this.lastPos = [fen, moves];
    } catch (e) {
      if (this.lastPos) { const [f, ms] = this.lastPos; this.lastPos = null; this.setPosition(f, ms); this.lastPos = [f, ms]; }
      else { pos.setFen(START_FEN); this._sendPosition(START_FEN, []); }
      throw e;
    }
    if (this.js) this.js.setPosition(fen, moves);
  }
  setUseNN(on) {
    this.useNN = !!on;
    if (!this.useNN && !this.js) {
      this.js = new JsSearcher({ hashMB: this.hashMB, nn: false });
      if (this.lastPos) this.js.setPosition(this.lastPos[0], this.lastPos[1]);
    }
    if (this.js) { this.js.externalStop = this.externalStop; this.js.setUseNN(false); }
  }
  elapsed() { return now() - this.startTime; }
  // те же правила времени, книги и searchmoves, что в JsSearcher.start
  start(limits) {
    limits = limits || {};
    if (!this.useNN) { this.js.externalStop = this.externalStop; return this.js.start(limits); }
    const pos = this.pos;
    this.limits = limits; this._stop = false; this.W.set_stop(0);
    this.startTime = now();
    let soft = 0, hard = 0;
    if (limits.movetime) { hard = Math.max(5, limits.movetime - 8); soft = limits.movetime * 0.95; }
    else if (limits.wtime !== undefined || limits.btime !== undefined) {
      const left = (pos.side === WHITE ? limits.wtime : limits.btime) || 0;
      const inc = (pos.side === WHITE ? limits.winc : limits.binc) || 0;
      const mtg = limits.movestogo ? Math.min(limits.movestogo, 40) : 30;
      const base = Math.max(10, left / mtg + inc * 0.75 - 30);
      soft = Math.min(base, left * 0.4);
      hard = Math.max(10, Math.min(base * 3, left * 0.6 - 50));
    }
    if (limits.infinite) { soft = 0; hard = 0; }
    if (this.externalStop) Atomics.store(this.externalStop, 0, 0);
    this.bookMove = null; this.lines = []; this.finished = false;
    if (limits.book) {
      const bm = pos.bookMoves();
      if (bm && pos.legalMoves().length) {
        const c = pickBookMove(bm);
        this.bookMove = c;
        this.lines = [{ move: c.m, score: 0, pv: [c.m], depth: 0 }];
        this.finished = true;
        return;
      }
    }
    let nSearch = 0;
    if (limits.searchmoves && limits.searchmoves.length) {
      const io = this._io();
      for (const u of limits.searchmoves) {
        const m = pos.uciToMove(u);
        if (m) io[nSearch++] = sq64(m & 127) | (sq64((m >> 7) & 127) << 6) | (((m >> 14) & 7) << 12);
      }
      if (!nSearch) io[nSearch++] = -1; // ни один ход не подошёл: искать нечего
    }
    const depth = Math.min(limits.depth || 0, MAX_PLY - 10);
    this.W.start(depth, soft, hard, limits.nodes || 0, limits.multipv || 1, limits.infinite ? 1 : 0, nSearch);
    this._read();
  }
  iterate() {
    if (!this.useNN) return this.js.iterate();
    if (this.finished || this._stop) return false;
    const more = !!this.W.iterate();
    this._read();
    if (!more) this.finished = true;
    return more;
  }
  _read() {
    const n = this.W.result(), io = this._io();
    let k = 0;
    const nl = io[k++];
    this.depthDone = io[k++]; this.selDepth = io[k++];
    if (io[k++]) this.finished = true;
    const lines = [];
    for (let i = 0; i < nl && k < n; i++) {
      const move = io[k++], score = io[k++], depth = io[k++], pn = io[k++];
      const pv = Array.from(io.subarray(k, k + pn)); k += pn;
      lines.push({ move, score, depth, pv });
    }
    this.lines = lines;
  }
  info() {
    if (!this.useNN) return this.js.info();
    const t = Math.max(1, this.elapsed()), nodes = this.bookMove ? 0 : this.W.nodes();
    return {
      depth: this.depthDone || (this.lines[0] ? this.lines[0].depth : 0),
      seldepth: this.selDepth || 0,
      nodes,
      time: Math.round(t),
      nps: Math.round(nodes * 1000 / t),
      hashfull: this.W.hashfull(),
      book: this.bookMove ? { n: this.bookMove.n, score: this.bookMove.score } : null,
      lines: this.lines.map(l => ({
        move: uciOfMove(l.move),
        score: l.score,
        cp: Math.abs(l.score) < MATE_BOUND ? Math.round(l.score * CP_SCALE) : null, // шкала Stockfish: см. CP_SCALE
        mate: Math.abs(l.score) >= MATE_BOUND ? (l.score > 0 ? Math.ceil((MATE - l.score) / 2) : -Math.ceil((MATE + l.score) / 2)) : null,
        pv: l.pv.map(m => uciOfMove(m)),
        depth: l.depth,
      })),
    };
  }
  run(limits, onInfo) {
    if (!this.useNN) return this.js.run(limits, onInfo);
    this.start(limits);
    while (this.iterate()) { if (onInfo) onInfo(this.info()); }
    const inf = this.info();
    if (onInfo) onInfo(inf);
    return inf;
  }
}

// Searcher: ядро на WebAssembly, если оно есть и загружена сеть в целых числах; иначе — поиск на JavaScript.
// opts.core === false — всегда JavaScript.
function Searcher(opts) {
  opts = opts || {};
  if (CORE_ON && opts.core !== false && opts.nn !== false && coreModule() && initNet() && NN.qa > 1) {
    try { return new CoreSearcher(opts); } catch (e) { /* не вышло — JavaScript */ }
  }
  return new JsSearcher(opts);
}
const coreAvailable = () => !!(CORE_ON && coreModule() && initNet() && NN && NN.qa > 1);

// ============================================================== Уровни сложности
// depth/movetime ограничивают поиск; multipv + temp/blunder делают ошибки «по-человечески».
const LEVELS = [
  null,
  { name: 'Beginner',       elo: 400,  depth: 1,  movetime: 250,  multipv: 6, temp: 260, blunder: 0.20 },
  { name: 'Novice',         elo: 650,  depth: 1,  movetime: 250,  multipv: 5, temp: 170, blunder: 0.10 },
  { name: 'Amateur',        elo: 900,  depth: 2,  movetime: 300,  multipv: 5, temp: 110, blunder: 0.05 },
  { name: 'Casual',         elo: 1150, depth: 3,  movetime: 400,  multipv: 4, temp: 70,  blunder: 0.02 },
  { name: 'Club player',    elo: 1400, depth: 4,  movetime: 500,  multipv: 4, temp: 45,  blunder: 0.01 },
  { name: 'Expert',         elo: 1650, depth: 6,  movetime: 700,  multipv: 3, temp: 28,  blunder: 0 },
  { name: 'Candidate',      elo: 1900, depth: 8,  movetime: 900,  multipv: 3, temp: 14,  blunder: 0 },
  { name: 'Master',         elo: 2100, depth: 12, movetime: 1300, multipv: 2, temp: 6,   blunder: 0 },
  { name: 'Grandmaster',    elo: 2300, depth: 0,  movetime: 2200, multipv: 1, temp: 0,   blunder: 0 },
  { name: 'Maximum',        elo: 2500, depth: 0,  movetime: 4500, multipv: 1, temp: 0,   blunder: 0 },
];

function levelLimits(level, ply) {
  const L = LEVELS[Math.max(1, Math.min(10, level | 0))];
  const lim = { movetime: L.movetime, multipv: L.multipv, book: level >= 3 };
  if (L.depth) lim.depth = L.depth;
  // разнообразие дебюта на сильных уровнях
  if (L.multipv === 1 && ply < 10) lim.multipv = 3;
  return lim;
}

// Выбор хода по результатам MultiPV с учётом уровня. rnd — функция [0,1).
function pickMove(info, level, ply, rnd) {
  rnd = rnd || Math.random;
  const L = LEVELS[Math.max(1, Math.min(10, level | 0))];
  const lines = info.lines.filter(l => l.move && l.move !== '0000');
  if (!lines.length) return null;
  const best = lines[0];
  // мат не упускаем начиная с 4 уровня
  if (best.mate !== null && best.mate > 0 && level >= 4) return best.move;
  const val = l => Math.max(-3000, Math.min(3000, l.score));
  if (L.temp === 0) {
    if (ply < 10 && lines.length > 1) {
      const ok = lines.filter(l => val(best) - val(l) <= 15);
      return ok[Math.floor(rnd() * ok.length)].move;
    }
    return best.move;
  }
  if (L.blunder && rnd() < L.blunder) return lines[Math.floor(rnd() * lines.length)].move;
  const bv = val(best);
  const w = lines.map(l => Math.exp((val(l) - bv) / L.temp));
  let sum = w.reduce((a, b) => a + b, 0), x = rnd() * sum;
  for (let i = 0; i < lines.length; i++) { x -= w[i]; if (x <= 0) return lines[i].move; }
  return best.move;
}

// ============================================================== Прогноз исхода
// Логистическая модель: из оценки (сантипешки за белых) и фазы партии —
// вероятности выигрыша белых, ничьей и выигрыша чёрных (в долях, сумма = 1).
function wdl(cp, mate, phase) {
  if (mate !== null && mate !== undefined) {
    return mate > 0 ? { w: 1, d: 0, l: 0 } : { w: 0, d: 0, l: 1 };
  }
  const ph = Math.max(0, Math.min(24, phase === undefined ? 24 : phase));
  const a = 85 + 55 * (1 - ph / 24); // в эндшпиле нужен больший перевес для победы
  const b = 72;
  const w = 1 / (1 + Math.exp(-(cp - a) / b));
  const l = 1 / (1 + Math.exp(-(-cp - a) / b));
  return { w, d: Math.max(0, 1 - w - l), l };
}
// «Шансы» в процентах 0..100 (как ожидаемый результат) — для классификации ходов
function winPercent(cp, mate) {
  if (mate !== null && mate !== undefined) return mate > 0 ? 100 : 0;
  return 50 + 50 * (2 / (1 + Math.exp(-0.00368208 * cp)) - 1);
}

// ============================================================== Классификация ходов
// before/after — оценки (cp, mate) с точки зрения игрока, сделавшего ход.
const MOVE_CLASSES = {
  brilliant:  { label: 'Brilliant',  sym: '!!', color: '#2bc0d0' },
  best:       { label: 'Best',       sym: '★',  color: '#4fae5a' },
  excellent:  { label: 'Excellent',  sym: '!',  color: '#86b83a' },
  good:       { label: 'Good',       sym: '✓',  color: '#86a883' },
  book:       { label: 'Book',       sym: '=',  color: '#8f84dc' },
  inaccuracy: { label: 'Inaccuracy', sym: '?!', color: '#e8b52c' },
  miss:       { label: 'Miss',       sym: '×',  color: '#e0558c' },
  mistake:    { label: 'Mistake',    sym: '?',  color: '#ec8130' },
  blunder:    { label: 'Blunder',    sym: '??', color: '#e0463f' },
};
const CLS_ORDER = ['brilliant', 'best', 'excellent', 'good', 'book', 'inaccuracy', 'miss', 'mistake', 'blunder'];
// o: { before:{cp,mate}, after:{cp,mate}, isBest, sacrifice, book — ход из дебютной книги,
//      prevErr — соперник только что ошибся (ошибка/зевок/промах) }
function classifyMove(o) {
  const wb = winPercent(o.before.cp, o.before.mate);
  const wa = winPercent(o.after.cp, o.after.mate);
  const loss = Math.max(0, wb - wa);
  let cls;
  if (o.isBest) cls = 'best';
  else if (loss < 2) cls = 'excellent';
  else if (loss < 6) cls = 'good';
  else if (loss < 12) cls = 'inaccuracy';
  else if (loss < 22) cls = 'mistake';
  else cls = 'blunder';
  // в уже решённых позициях проценты почти не меняются — учитываем и потерю в пешках
  if (!o.isBest && o.before.cp !== null && o.after.cp !== null) {
    const cpLoss = o.before.cp - o.after.cp;
    const atLeast = (c) => { if (CLS_ORDER.indexOf(c) > CLS_ORDER.indexOf(cls)) cls = c; };
    if (cpLoss >= 500) atLeast('mistake');
    else if (cpLoss >= 250) atLeast('inaccuracy');
    else if (cpLoss >= 100) atLeast('good');
  }
  // проигрывать уже проигранную позицию — не зевок
  if (cls === 'blunder' && wb < 6) cls = 'mistake';
  // промах: соперник подставился, а шанс не использован (но и не всё испорчено)
  if (o.prevErr && wb >= 65 && wa >= 30 && (cls === 'inaccuracy' || cls === 'mistake' || cls === 'blunder')) cls = 'miss';
  if (o.sacrifice && (o.isBest || loss < 1.5) && wa >= 45 && wb < 97) cls = 'brilliant';
  else if (o.book && loss < 12) cls = 'book';
  return { cls, loss, accuracy: moveAccuracy(wb, wa), winBefore: wb, winAfter: wa };
}

// Точность хода по изменению шансов (формула lichess)
function moveAccuracy(before, after) {
  if (after >= before) return 100;
  const a = 103.1668 * Math.exp(-0.04354 * (before - after)) - 3.1669 + 1;
  return Math.max(0, Math.min(100, a));
}

// Точность за партию (как на lichess): среднее, взвешенное по «остроте» позиции,
// плюс гармоническое среднее, которое сильно наказывает за грубые ошибки.
// winPcts — шансы белых (0..100) для каждой позиции; firstColor — кто сделал первый ход.
function gameAccuracy(winPcts, firstColor) {
  const n = winPcts.length;
  const res = { white: null, black: null };
  if (n < 2) return res;
  const ws = Math.max(2, Math.min(8, Math.floor(n / 10)));
  const windows = [];
  for (let i = 0; i < Math.min(ws, n) - 2; i++) windows.push(winPcts.slice(0, ws));
  for (let i = 0; i + ws <= n; i++) windows.push(winPcts.slice(i, i + ws));
  const sd = (xs) => { const m = xs.reduce((a, b) => a + b, 0) / xs.length; return Math.sqrt(xs.reduce((a, b) => a + (b - m) * (b - m), 0) / xs.length); };
  const weights = windows.map(w => Math.max(0.5, Math.min(12, sd(w))));
  const acc = [[], []];
  for (let i = 0; i < n - 1; i++) {
    const color = (firstColor + i) & 1;
    const prev = winPcts[i], next = winPcts[i + 1];
    const a = color === 0 ? moveAccuracy(prev, next) : moveAccuracy(100 - prev, 100 - next);
    acc[color].push([a, weights[i] || 1]);
  }
  for (let c = 0; c < 2; c++) {
    const xs = acc[c];
    if (!xs.length) continue;
    const wsum = xs.reduce((s, x) => s + x[1], 0);
    const wmean = xs.reduce((s, x) => s + x[0] * x[1], 0) / wsum;
    const hmean = xs.length / xs.reduce((s, x) => s + 1 / Math.max(x[0], 1), 0);
    res[c === 0 ? 'white' : 'black'] = (wmean + hmean) / 2;
  }
  return res;
}

// Жертва: ход фигурой (не пешкой) на поле, где её можно выгодно забрать
function isSacrifice(pos, m) {
  const from = m & 127, to = (m >> 7) & 127;
  const p = pos.board[from], t = p & 7;
  if (t === PAWN || t === KING || ((m >> 14) & 7)) return false;
  const capVal = pos.board[to] ? SEE_VAL[pos.board[to] & 7] : 0;
  if (!pos.make(m)) return false;
  // может ли соперник взять фигуру с выигрышем
  let sac = false;
  const buf = new Int32Array(256);
  const n = pos.genMoves(buf, 0, false);
  for (let i = 0; i < n; i++) {
    if (((buf[i] >> 7) & 127) !== to) continue;
    const g = pos.see(buf[i]);
    if (g > 0 && SEE_VAL[t] - capVal >= 200) { sac = true; break; }
  }
  pos.unmake();
  return sac;
}

// ============================================================== PGN
// Разбирает первую партию из текста PGN (chess.com, lichess и др.).
// Возвращает { headers, startFen, moves: [uci], result, error }.
function parsePgn(text) {
  text = String(text || '').replace(/\r/g, '').replace(/^\uFEFF/, '');
  // только первая партия
  const second = text.search(/\n\s*\n\s*\[Event /);
  if (second > 0 && /\S/.test(text.slice(0, second).replace(/^\s*\[[^\]]*\]\s*$/gm, ''))) text = text.slice(0, second);
  const headers = {};
  const hre = /^\s*\[(\w+)\s+"((?:[^"\\]|\\.)*)"\s*\]\s*$/gm;
  let m;
  while ((m = hre.exec(text))) headers[m[1]] = m[2].replace(/\\"/g, '"');
  let body = text.replace(/^\s*\[[^\]]*\]\s*$/gm, ' ');
  body = body.replace(/\{[^}]*\}/g, ' ').replace(/;[^\n]*/g, ' ');
  let prev;
  do { prev = body; body = body.replace(/\([^()]*\)/g, ' '); } while (body !== prev);
  body = body.replace(/\$\d+/g, ' ');
  const tokens = body.split(/\s+/).filter(Boolean);
  let pos;
  try { pos = new Position().setFen(headers.FEN || START_FEN); }
  catch (e) { return { headers, startFen: START_FEN, moves: [], result: '*', error: 'Invalid position in the FEN tag' }; }
  const startFen = pos.fen();
  const moves = [];
  let result = headers.Result || '*', error = null;
  for (let tok of tokens) {
    if (/^(1-0|0-1|1\/2-1\/2|\*)$/.test(tok)) { result = tok; break; }
    tok = tok.replace(/^\d+\.+/, '').replace(/^\.+/, '');
    if (!tok || /^\d+$/.test(tok)) continue;
    const mv = pos.parseSan(tok);
    if (!mv) { error = `Could not read the move “${tok}” (after ${moves.length} plies)`; break; }
    moves.push(pos.moveToUci(mv));
    pos.make(mv);
  }
  if (!moves.length && !error && !headers.FEN) error = 'No moves found in the text';
  return { headers, startFen, moves, result, error };
}

// ============================================================== Дебютная книга
// Данные кладёт engine/book.js в globalThis.BLIZZARD_BOOK (base64); разбираются при первом обращении.
let BOOK = null;
function b64bytes(str) {
  if (typeof Buffer !== 'undefined' && typeof atob === 'undefined') return new Uint8Array(Buffer.from(str, 'base64'));
  const bin = atob(str), u = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) u[i] = bin.charCodeAt(i);
  return u;
}
function bookData() {
  if (BOOK !== null) return BOOK;
  const src = global.BLIZZARD_BOOK;
  if (!src) return (BOOK = false);
  try {
    const u = b64bytes(src), dv = new DataView(u.buffer, u.byteOffset, u.byteLength);
    let o = 0;
    const n = dv.getUint32(o, true); o += 4;
    const hi = new Uint32Array(n), lo = new Uint32Array(n), start = new Uint32Array(n + 1);
    let tot = 0;
    for (let i = 0; i < n; i++) { hi[i] = dv.getUint32(o, true); lo[i] = dv.getUint32(o + 4, true); start[i] = tot; tot += dv.getUint8(o + 8); o += 9; }
    start[n] = tot;
    const mv = new Uint16Array(tot), cnt = new Uint16Array(tot), sc = new Uint8Array(tot);
    for (let j = 0; j < tot; j++) { mv[j] = dv.getUint16(o, true); cnt[j] = dv.getUint16(o + 2, true); sc[j] = dv.getUint8(o + 4); o += 5; }
    const nn = dv.getUint32(o, true); o += 4;
    const nhi = new Uint32Array(nn), nlo = new Uint32Array(nn), nidx = new Uint16Array(nn);
    for (let i = 0; i < nn; i++) { nhi[i] = dv.getUint32(o, true); nlo[i] = dv.getUint32(o + 4, true); nidx[i] = dv.getUint16(o + 8, true); o += 10; }
    const len = dv.getUint32(o, true); o += 4;
    const names = new TextDecoder('utf-8').decode(u.subarray(o, o + len)).split('\n');
    BOOK = { n, hi, lo, start, mv, cnt, sc, nn, nhi, nlo, nidx, names };
  } catch (e) { BOOK = false; }
  return BOOK;
}
function bsearch(H, L, n, h, l) {
  let a = 0, b = n - 1;
  while (a <= b) {
    const m = (a + b) >> 1;
    if (H[m] < h || (H[m] === h && L[m] < l)) a = m + 1;
    else if (H[m] > h || L[m] > l) b = m - 1;
    else return m;
  }
  return -1;
}
// Ходы из книги для позиции: [{ m, uci, n — сколько раз сыграно, score — результат для ходящего 0..1 }]
Position.prototype.bookMoves = function () {
  const B = bookData();
  if (!B) return null;
  const i = bsearch(B.hi, B.lo, B.n, this.hashHi >>> 0, this.hashLo >>> 0);
  if (i < 0) return null;
  const legal = this.legalMoves(), out = [];
  for (let j = B.start[i]; j < B.start[i + 1]; j++) {
    const v = B.mv[j], f = v & 63, t = (v >> 6) & 63, pr = (v >> 12) & 7;
    const from = (f >> 3) * 16 + (f & 7), to = (t >> 3) * 16 + (t & 7);
    const m = legal.find((x) => (x & 127) === from && ((x >> 7) & 127) === to && ((x >> 14) & 7) === pr);
    if (m) out.push({ m, uci: this.moveToUci(m), n: B.cnt[j], score: B.sc[j] / 255 });
  }
  return out.length ? out : null;
};
// Название дебюта для позиции (если есть в справочнике)
Position.prototype.openingName = function () {
  const B = bookData();
  if (!B) return null;
  const i = bsearch(B.nhi, B.nlo, B.nn, this.hashHi >>> 0, this.hashLo >>> 0);
  return i < 0 ? null : B.names[B.nidx[i]];
};
function pickBookMove(list, rnd) {
  rnd = rnd || Math.random;
  let ok = list.filter((x) => x.n >= 3 && (x.score >= 0.36 || x.n >= 40));
  if (!ok.length) ok = list;
  const w = ok.map((x) => Math.pow(x.n, 0.9));
  let r = rnd() * w.reduce((a, b) => a + b, 0);
  for (let i = 0; i < ok.length; i++) { r -= w[i]; if (r <= 0) return ok[i]; }
  return ok[0];
}

// ============================================================== Экспорт
const Blizzard = {
  NAME, VERSION, START_FEN, WHITE, BLACK, MATE, MATE_BOUND,
  Position, Searcher, JsSearcher, CoreSearcher, coreAvailable, setCore, CORE_PARAMS, TransTable, LEVELS, levelLimits, pickMove, wdl, winPercent,
  classifyMove, isSacrifice, moveAccuracy, gameAccuracy, MOVE_CLASSES, sqName, parseSq, parsePgn,
  TERMS, TI, get NTERMS() { return NTERMS; }, defaultParams, setParams, getParams: () => Int32Array.from(W),
  bookData, pickBookMove,
  initNet, setNetQuant, setNetWasm, hasNet: () => !!initNet(), netWasm: () => !!(NN_USE_WASM && nnWasmModule()), netInfo: () => (initNet() ? { hidden: NN.H, buckets: NN.NB, kingBuckets: NN.KB, inputs: NN.NI } : null), netRaw: () => (initNet() ? NN : null),
};

if (typeof module !== 'undefined' && module.exports) module.exports = Blizzard;
global.Blizzard = Blizzard;

// ============================================================== Web Worker
// Протокол сообщений:
//   → { type:'go', id, fen, moves, limits }   ← { type:'info', id, ... }, { type:'done', id, ... }
//   → { type:'stop' }  → { type:'newgame' }
const isWorker = typeof WorkerGlobalScope !== 'undefined' && typeof self !== 'undefined' && self instanceof WorkerGlobalScope;
if (isWorker) attachWorker(self);

function attachWorker(scope) {
  const searcher = new Searcher({ hashMB: 32 });
  let job = null;
  // быстрый «уступ» потоку сообщений между итерациями (без задержки setTimeout)
  const schedule = (typeof MessageChannel !== 'undefined') ? (() => {
    const ch = new MessageChannel(), q = [];
    ch.port1.onmessage = () => { const f = q.shift(); if (f) f(); };
    return (f) => { q.push(f); ch.port2.postMessage(0); };
  })() : (f) => setTimeout(f, 0);
  function step(j) {
    if (job !== j) return;
    const t0 = now();
    let more;
    try { do { more = searcher.iterate(); } while (more && now() - t0 < 20); }
    catch (e) { scope.postMessage({ type: 'error', id: j.id, message: String(e && e.message || e) }); job = null; return; }
    const inf = searcher.info();
    if (more) {
      scope.postMessage(Object.assign({ type: 'info', id: j.id }, inf));
      schedule(() => step(j));
    } else {
      job = null;
      scope.postMessage(Object.assign({ type: 'done', id: j.id }, inf));
    }
  }
  scope.onmessage = (ev) => {
    const msg = ev.data || {};
    if (msg.type === 'go') {
      try {
        searcher.setPosition(msg.fen, msg.moves);
        searcher.start(msg.limits || {});
      } catch (e) {
        scope.postMessage({ type: 'error', id: msg.id, message: String(e && e.message || e) });
        return;
      }
      job = { id: msg.id };
      const j = job;
      schedule(() => step(j));
    } else if (msg.type === 'stop') {
      if (job) { const j = job; job = null; searcher.stop = true; scope.postMessage(Object.assign({ type: 'done', id: j.id, stopped: true }, searcher.info())); }
    } else if (msg.type === 'newgame') {
      job = null; searcher.newGame();
    }
  };
  scope.postMessage({ type: 'ready', name: NAME, version: VERSION });
}
Blizzard.attachWorker = attachWorker;

})(typeof globalThis !== 'undefined' ? globalThis : this);
