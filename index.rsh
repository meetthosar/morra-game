'reach 0.1';

const Guess = Object({
  hand : UInt,
  guess : UInt
});

const commonFunction = {
  ...hasRandom,
  playHandAndGuess : Fun([],Guess),
  seeWinner : Fun([Address],Null),
}

const [isOutcome, DRAW,PLAYER1_WINS, PLAYER2_WINS] = makeEnum(3);

const winnerGuess = (handPlayer1, handPlayer2) =>  handPlayer1 + handPlayer2;

const winner = (hand1, guessP1, hand2, guessP2) => (winnerGuess(hand1, hand2) == guessP1) ? PLAYER1_WINS : ((winnerGuess(hand1, hand2) == guessP2) ? PLAYER2_WINS : DRAW)
  

export const main = Reach.App(() => {
  const Player1 = Participant('Player1', {
    ...commonFunction,
    startGame : Fun([], Null),
    wager : UInt,
    deadline : UInt
  });
  const Player2 = Participant('Player2', {
    ...commonFunction,
    acceptWager : Fun([],Null),
  });
  init();
  // The first one to publish deploys the contract

  Player1.only(() => {
    const wager = declassify(interact.wager);
    const deadline = declassify(interact.deadline);
  });

  Player1.publish(wager, deadline).pay(wager);
  commit();
  
  
  Player2.only(() => {
    interact.acceptWager();
     
  });
  Player2.pay(wager);


  var outcome = DRAW;
  invariant( balance() == 2 * wager && isOutcome(outcome))
  while( outcome == DRAW ){

    commit();

    Player1.only(() => {
      const _guessP1 = interact.playHandAndGuess();
      const [_commitmentP1, _salt] = makeCommitment(interact, _guessP1);
      const commitP1 = declassify(_commitmentP1);
    });

    Player1.publish(commitP1);
    commit();


    unknowable(Player2, Player1(_guessP1, _salt));
    Player2.only(() => {
      const guessP2 = declassify(interact.playHandAndGuess());
    })

    Player2.publish(guessP2);
    commit();

    Player1.only(() => {
      const saltP1 = declassify(_salt);
      const guessP1 = declassify(_guessP1);
    });

    Player1.publish(saltP1, guessP1);
    checkCommitment(commitP1, saltP1, guessP1);

    outcome = winner(guessP1.hand, guessP1.guess, guessP2.hand, guessP2.guess);
    continue;
    // commit();
    // write your program here
    
}

assert(outcome == PLAYER1_WINS || outcome == PLAYER2_WINS)
transfer(2 * wager).to(outcome == PLAYER1_WINS? Player1 : Player2);
  commit();
  exit();
});
