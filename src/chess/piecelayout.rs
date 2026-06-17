use std::fmt::Display;

use crate::{
    chess::{
        board::movegen::{
            self, RAY_BETWEEN, diag_attacks, king_attacks, knight_attacks, orth_attacks,
            pawn_attacks, pawn_attacks_by,
        },
        piece::{Black, Col, Colour, Piece, PieceType, White},
        squareset::SquareSet,
        types::{File, Rank, Square},
    },
    evaluation::{DOUBLED_PAWN_MASKS, PASSED_PAWN_MASKS},
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub struct PieceLayout {
    pub pieces: [SquareSet; 6],
    pub colours: [SquareSet; 2],
}

impl PieceLayout {
    pub fn occupied(&self) -> SquareSet {
        self.colours[Colour::White] | self.colours[Colour::Black]
    }

    pub fn empty(&self) -> SquareSet {
        !self.occupied()
    }

    pub fn move_piece(&mut self, from: Square, to: Square, piece: Piece) {
        let from_to_bb = from.as_set() | to.as_set();
        self.pieces[piece.piece_type()] ^= from_to_bb;
        self.colours[piece.colour()] ^= from_to_bb;
    }

    pub fn set_piece_at(&mut self, sq: Square, piece: Piece) {
        let sq_bb = sq.as_set();
        self.pieces[piece.piece_type()] |= sq_bb;
        self.colours[piece.colour()] |= sq_bb;
    }

    pub fn clear_piece_at(&mut self, sq: Square, piece: Piece) {
        let sq_bb = sq.as_set();
        self.pieces[piece.piece_type()] &= !sq_bb;
        self.colours[piece.colour()] &= !sq_bb;
    }

    pub fn piece_bb(&self, piece: Piece) -> SquareSet {
        SquareSet::intersection(
            self.pieces[piece.piece_type()],
            self.colours[piece.colour()],
        )
    }

    pub fn all_attackers_to_sq(&self, sq: Square, occupied: SquareSet) -> SquareSet {
        let sq_bb = sq.as_set();
        let black_pawn_attackers = pawn_attacks::<White>(sq_bb)
            & self.pieces[PieceType::Pawn]
            & self.colours[Colour::Black];
        let white_pawn_attackers = pawn_attacks::<Black>(sq_bb)
            & self.pieces[PieceType::Pawn]
            & self.colours[Colour::White];
        let knight_attackers = knight_attacks(sq) & (self.pieces[PieceType::Knight]);
        let diag_attackers = diag_attacks(sq, occupied)
            & (self.pieces[PieceType::Bishop] | self.pieces[PieceType::Queen]);
        let orth_attackers = orth_attacks(sq, occupied)
            & (self.pieces[PieceType::Rook] | self.pieces[PieceType::Queen]);
        let king_attackers = king_attacks(sq) & (self.pieces[PieceType::King]);
        black_pawn_attackers
            | white_pawn_attackers
            | knight_attackers
            | diag_attackers
            | orth_attackers
            | king_attackers
    }

    /// Determines if `sq` is attacked by `side`
    pub fn sq_attacked(&self, sq: Square, side: Colour) -> bool {
        match side {
            Colour::White => self.sq_attacked_by::<White>(sq),
            Colour::Black => self.sq_attacked_by::<Black>(sq),
        }
    }

    pub fn sq_attacked_by<C: Col>(&self, sq: Square) -> bool {
        use PieceType::{Bishop, King, Knight, Pawn, Queen, Rook};

        let attackers = self.colours[C::COLOUR];

        // pawns
        if pawn_attacks::<C>(self.pieces[Pawn] & attackers).contains_square(sq) {
            return true;
        }

        // knights
        if (attackers & self.pieces[Knight]) & movegen::knight_attacks(sq) != SquareSet::EMPTY {
            return true;
        }

        let blockers = attackers | self.colours[!C::COLOUR];

        // bishops, queens
        let diags = attackers & (self.pieces[Queen] | self.pieces[Bishop]);
        if diags & movegen::diag_attacks(sq, blockers) != SquareSet::EMPTY {
            return true;
        }

        // rooks, queens
        let orthos = attackers & (self.pieces[Queen] | self.pieces[Rook]);
        if orthos & movegen::orth_attacks(sq, blockers) != SquareSet::EMPTY {
            return true;
        }

        // king
        if (attackers & self.pieces[King]) & movegen::king_attacks(sq) != SquareSet::EMPTY {
            return true;
        }

        false
    }

    pub fn piece_at(&self, sq: Square) -> Option<Piece> {
        let sq_bb = sq.as_set();
        let colour = if (self.colours[Colour::White] & sq_bb) != SquareSet::EMPTY {
            Colour::White
        } else if (self.colours[Colour::Black] & sq_bb) != SquareSet::EMPTY {
            Colour::Black
        } else {
            return None;
        };
        for piece in PieceType::all() {
            if (self.pieces[piece] & sq_bb) != SquareSet::EMPTY {
                return Some(Piece::new(colour, piece));
            }
        }
        panic!(
            "Bit set in colour square-set for {colour:?} but not in piece square-sets! square is {sq}"
        );
    }

    fn any_bbs_overlapping(&self) -> bool {
        if (self.colours[0] & self.colours[1]) != SquareSet::EMPTY {
            return true;
        }
        for i in 0..self.pieces.len() {
            for j in i + 1..self.pieces.len() {
                if (self.pieces[i] & self.pieces[j]) != SquareSet::EMPTY {
                    return true;
                }
            }
        }
        false
    }

    /// Computes the set of “phantom” passed-pawn feature squares for each colour.
    ///
    /// A non-doubled passed pawn on file `f` is encoded as a pawn of its own
    /// colour standing on the back rank (rank 1 for White, rank 8 for Black) of
    /// file `f`. These pawn-plane squares can never be occupied by a real pawn,
    /// so they are repurposed as passed-pawn markers without colliding with the
    /// ordinary piece-square features. The passer weights live in the pawn
    /// matrix, so feeding these through the usual feature-indexing path is
    /// sufficient.
    ///
    /// TODO: Do these need to be two separate bitboards?
    pub fn passer_features(&self) -> [SquareSet; 2] {
        let white_pawns = self.pieces[PieceType::Pawn] & self.colours[Colour::White];
        let black_pawns = self.pieces[PieceType::Pawn] & self.colours[Colour::Black];

        let mut white = SquareSet::EMPTY;
        for sq in white_pawns {
            // a pawn is passed if no enemy pawn lies in front on the same or
            // adjacent files, and not doubled if no friendly pawn lies in front
            // on the same file.
            let passed = (black_pawns.inner() & PASSED_PAWN_MASKS[sq.index()]) == 0;
            let doubled = (white_pawns.inner() & DOUBLED_PAWN_MASKS[sq.index()]) != 0;
            if passed && !doubled {
                white |= Square::from_rank_file(Rank::One, sq.file()).as_set();
            }
        }

        // black is handled by vertically mirroring the board, so we can reuse
        // the white-oriented masks (cf. the trainer-side feature generation).
        let mut black = SquareSet::EMPTY;
        let white_pawns_flipped = white_pawns.inner().swap_bytes();
        let black_pawns_flipped = black_pawns.inner().swap_bytes();
        for sq in black_pawns {
            let flipped = sq.flip_rank().index();
            let passed = (white_pawns_flipped & PASSED_PAWN_MASKS[flipped]) == 0;
            let doubled = (black_pawns_flipped & DOUBLED_PAWN_MASKS[flipped]) != 0;
            if passed && !doubled {
                black |= Square::from_rank_file(Rank::Eight, sq.file()).as_set();
            }
        }

        [white, black]
    }

    /// Calls `callback` for each piece that is added or removed from `self` to `target`.
    pub fn update_iter(&self, target: Self, mut callback: impl FnMut(Square, Piece, bool)) {
        for colour in Colour::all() {
            for piece_type in PieceType::all() {
                let piece = Piece::new(colour, piece_type);
                let source_bb = self.pieces[piece_type] & self.colours[colour];
                let target_bb = target.pieces[piece_type] & target.colours[colour];
                let added = target_bb & !source_bb;
                let removed = source_bb & !target_bb;
                for sq in added {
                    callback(sq, piece, true);
                }
                for sq in removed {
                    callback(sq, piece, false);
                }
            }
        }

        // Diff the passed-pawn marker features. These are emitted as pawns
        // standing on the back rank, which the feature-indexing path treats
        // exactly like ordinary pawn features.
        let source_passers = self.passer_features();
        let target_passers = target.passer_features();
        for colour in Colour::all() {
            let piece = Piece::new(colour, PieceType::Pawn);
            let added = target_passers[colour] & !source_passers[colour];
            let removed = source_passers[colour] & !target_passers[colour];
            for sq in added {
                callback(sq, piece, true);
            }
            for sq in removed {
                callback(sq, piece, false);
            }
        }
    }

    pub fn visit_pieces(&self, mut callback: impl FnMut(Square, Piece)) {
        for colour in Colour::all() {
            for piece_type in PieceType::all() {
                let piece = Piece::new(colour, piece_type);
                let bb = self.pieces[piece_type] & self.colours[colour];
                for sq in bb {
                    callback(sq, piece);
                }
            }
        }
    }

    /// Returns true if the current position *would* be a draw by insufficient material,
    /// if there were no pawns on the board.
    pub fn is_material_draw(&self) -> bool {
        let white = self.colours[Colour::White];
        let black = self.colours[Colour::Black];
        let bishops = self.pieces[PieceType::Bishop];
        let knights = self.pieces[PieceType::Knight];
        let rooks = self.pieces[PieceType::Rook];
        let queens = self.pieces[PieceType::Queen];
        let wb = bishops & white;
        let bb = bishops & black;
        let wn = knights & white;
        let bn = knights & black;
        let wr = rooks & white;
        let br = rooks & black;
        if queens != SquareSet::EMPTY {
            return false;
        }
        if rooks == SquareSet::EMPTY {
            if bishops == SquareSet::EMPTY {
                if wn.count() < 3 && bn.count() < 3 {
                    return true;
                }
            } else if knights == SquareSet::EMPTY && wb.count().abs_diff(bb.count()) < 2
                || (wb | wn).count() == 1 && (bb | bn).count() == 1
            {
                return true;
            }
        } else if wr.count() == 1 && br.count() == 1 {
            if (wn | wb).count() < 2 && (bn | bb).count() < 2 {
                return true;
            }
        } else if wr.count() == 1 && br == SquareSet::EMPTY {
            if (wn | wb) == SquareSet::EMPTY && ((bn | bb).count() == 1 || (bn | bb).count() == 2) {
                return true;
            }
        } else if wr == SquareSet::EMPTY
            && br.count() == 1
            && (bn | bb) == SquareSet::EMPTY
            && ((wn | wb).count() == 1 || (wn | wb).count() == 2)
        {
            return true;
        }
        false
    }

    pub fn king_sq(&self, colour: Colour) -> Square {
        let king_bb = self.pieces[PieceType::King] & self.colours[colour];
        debug_assert_eq!(king_bb.count(), 1);
        king_bb.first().unwrap()
    }

    pub fn generate_pinned(&self, side: Colour) -> SquareSet {
        use PieceType::{Bishop, Queen, Rook};

        let mut pinned = SquareSet::EMPTY;

        let king = self.king_sq(side);

        let us = self.colours[side];
        let them = self.colours[!side];

        let their_diags = (self.pieces[Queen] | self.pieces[Bishop]) & them;
        let their_orthos = (self.pieces[Queen] | self.pieces[Rook]) & them;

        let potential_attackers =
            diag_attacks(king, them) & their_diags | orth_attacks(king, them) & their_orthos;

        for potential_attacker in potential_attackers {
            let maybe_pinned = us & RAY_BETWEEN[king][potential_attacker];
            if maybe_pinned.one() {
                pinned |= maybe_pinned;
            }
        }

        pinned
    }

    pub fn generate_threats(&self, side: Colour) -> Threats {
        let mut checkers = SquareSet::EMPTY;

        let us = self.colours[side];
        let them = self.colours[!side];
        let their_pawns = self.pieces[PieceType::Pawn] & them;
        let their_knights = self.pieces[PieceType::Knight] & them;
        let their_bishops = self.pieces[PieceType::Bishop] & them;
        let their_rooks = self.pieces[PieceType::Rook] & them;
        let their_queens = self.pieces[PieceType::Queen] & them;
        let their_king = (self.pieces[PieceType::King] & them).first().unwrap();
        let blockers = us | them;

        // compute threats
        let leq_pawn = match side {
            Colour::White => their_pawns.south_east_one() | their_pawns.south_west_one(),
            Colour::Black => their_pawns.north_east_one() | their_pawns.north_west_one(),
        };

        let mut leq_minor = leq_pawn;
        for sq in their_knights {
            leq_minor |= knight_attacks(sq);
        }
        for sq in their_bishops {
            leq_minor |= diag_attacks(sq, blockers);
        }
        let mut leq_rook = leq_minor;
        for sq in their_rooks {
            leq_rook |= orth_attacks(sq, blockers);
        }
        let mut all_threats = leq_rook;
        for sq in their_queens {
            all_threats |= diag_attacks(sq, blockers);
            all_threats |= orth_attacks(sq, blockers);
        }
        all_threats |= king_attacks(their_king);

        // compute checkers
        let our_king_bb = us & self.pieces[PieceType::King];
        let our_king_sq = our_king_bb.first().unwrap();
        let backwards_from_king = match side {
            Colour::White => our_king_bb.north_east_one() | our_king_bb.north_west_one(),
            Colour::Black => our_king_bb.south_east_one() | our_king_bb.south_west_one(),
        };
        checkers |= backwards_from_king & their_pawns;
        let from_knight = knight_attacks(our_king_sq);
        checkers |= from_knight & their_knights;
        let from_diag = diag_attacks(our_king_sq, blockers);
        checkers |= from_diag & (their_bishops | their_queens);
        let from_orth = orth_attacks(our_king_sq, blockers);
        checkers |= from_orth & (their_rooks | their_queens);

        let mut tellers = [SquareSet::EMPTY; 6];
        tellers[PieceType::Pawn] = pawn_attacks_by(their_king.as_set(), !side);
        tellers[PieceType::Knight] = knight_attacks(their_king);
        tellers[PieceType::Bishop] = diag_attacks(their_king, blockers);
        tellers[PieceType::Rook] = orth_attacks(their_king, blockers);
        tellers[PieceType::Queen] = tellers[PieceType::Bishop] | tellers[PieceType::Rook];

        Threats {
            all: all_threats,
            leq_pawn,
            leq_minor,
            leq_rook,
            checkers,
            tellers,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub struct Threats {
    pub all: SquareSet,
    pub leq_pawn: SquareSet,
    pub leq_minor: SquareSet,
    pub leq_rook: SquareSet,
    pub checkers: SquareSet,
    pub tellers: [SquareSet; 6],
}

impl Display for PieceLayout {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for rank in Rank::all().rev() {
            for file in File::all() {
                let sq = Square::from_rank_file(rank, file);
                if let Some(piece) = self.piece_at(sq) {
                    write!(f, " {}", piece.char())?;
                } else {
                    write!(f, " .")?;
                }
            }
            writeln!(f)?;
        }
        if self.any_bbs_overlapping() {
            writeln!(f, "WARNING: Some square-sets are overlapping")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{PieceLayout, SquareSet};
    use crate::chess::{
        piece::{Piece, PieceType},
        types::Square,
    };

    /// Builds the layout for `k7/8/2pp4/8/7P/4PP1P/8/7K`, the same board used
    /// in the `feature_generation` test in bullet. One pawn of each colour
    /// is passed; the doubled white h-pawn is not.
    fn passer_test_layout() -> PieceLayout {
        let mut bbs = PieceLayout::default();
        bbs.set_piece_at(Square::A8, Piece::BK);
        bbs.set_piece_at(Square::C6, Piece::BP);
        bbs.set_piece_at(Square::D6, Piece::BP);
        bbs.set_piece_at(Square::H4, Piece::WP);
        bbs.set_piece_at(Square::E3, Piece::WP);
        bbs.set_piece_at(Square::F3, Piece::WP);
        bbs.set_piece_at(Square::H3, Piece::WP);
        bbs.set_piece_at(Square::H1, Piece::WK);
        bbs
    }

    #[test]
    fn passer_features_match_expected() {
        let bbs = passer_test_layout();
        let [white, black] = bbs.passer_features();

        // White: f3 is passed (e3 is blocked by d6, h4 passed but h3 doubled),
        // so the white markers sit on f1 and h1.
        assert_eq!(white, Square::F1.as_set() | Square::H1.as_set());
        // Black: c6 is passed (d6 is blocked by e3), so the marker sits on c8.
        assert_eq!(black, Square::C8.as_set());
    }

    #[test]
    fn update_iter_emits_passer_diffs() {
        let bbs = passer_test_layout();

        // From an empty layout, every passer marker should be added.
        let mut added = SquareSet::EMPTY;
        let mut removed = SquareSet::EMPTY;
        PieceLayout::default().update_iter(bbs, |sq, piece, is_add| {
            // back-rank pawns are the passer markers (real pawns can't be there).
            if piece.piece_type() == PieceType::Pawn
                && matches!(
                    sq.rank(),
                    crate::chess::types::Rank::One | crate::chess::types::Rank::Eight
                )
            {
                if is_add {
                    added |= sq.as_set();
                } else {
                    removed |= sq.as_set();
                }
            }
        });
        assert_eq!(
            added,
            Square::F1.as_set() | Square::H1.as_set() | Square::C8.as_set()
        );
        assert_eq!(removed, SquareSet::EMPTY);

        // Identity transition emits no passer changes.
        let mut touched = false;
        bbs.update_iter(bbs, |sq, _piece, _is_add| {
            if matches!(
                sq.rank(),
                crate::chess::types::Rank::One | crate::chess::types::Rank::Eight
            ) {
                touched = true;
            }
        });
        assert!(!touched, "identity update should not touch passer features");
    }
}
