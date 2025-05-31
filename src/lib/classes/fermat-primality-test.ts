import { LargePowerModulo } from './large-power-modulo';
import {
  LoggerType,
} from '../types/logger.type';
import {
  getRandomNumber,
  sup,
} from '../utility';
import { logger } from './logger';


// https://---------.io/utC37e3uQpr1dRD8WJD9NM
// 8-30
//

/**
 * Fermat primality test
 * */
export class FermatPrimalityTest {
  // allows to use a customer logger
  logger: LoggerType = logger;

  // test number
  // biggest prime that we can test - 9007199254740881
  // biggest composite - 9007199254740991
  n: number = 9007199254740991; // 9007199254740881

  // numberOfIterations
  k: number = 10;

  constructor(n?: number, k?: number) {
    if (typeof n !== 'undefined') {
      this.n = n;
    }
    if (typeof k !== 'undefined') {
      this.k = k;
    }
  }

  /**
   * Set a number to test
   * @param testNumber 
   */
  setNumber(testNumber: number): void {
    this.n = testNumber;
    if (this.isEven()) {
      this.logger.warn(`${testNumber} is even. Prime number cannot be even.`);
    }
  }

  /**
   * Set the number of interations for running the test
   * @param testNumber 
   */
  setNumberOfIterations(num: number): void {
    this.k = num;
  }

  /**
   * Prime number cannot be even
   * @returns 
   */
  isEven() {
    return this.n % 2 === 0;
  }

  /**
   * Run the test
   */
  isPrime(): boolean {
    this.logger.log(`☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰☰`);
    this.logger.log(`Тест Ферма на простоту. n=${this.n}, k=${this.k}\n`);

    if (this.isEven()) {
      this.logger.log(`${this.n} is even. It is not prime.`);
      return false;
    }

    let numberIsPrime: boolean = true;

    this.logger.log(`\n\t\t\tСлучайное число\tr\tСоставное\t\n`);

    for (let i = 0; i < this.k; i++) {
      // step 1
      const randomNumber: number = this.getRandomNumber();
      // step 2
      const r = this.calculateR(randomNumber);
      // step 3
      const isC = this.isComposite(r);
      this.logger.log(`\tИтерация ${i + 1}: \t${randomNumber}\t${r}\t${isC}\t\n`);

      if (isC) {
        numberIsPrime = false;
        break;
      }
    }
    this.logger.log(``);

    if (numberIsPrime) {
      const probability: number = 1 / 2 ** this.k;
      this.logger.log(`${this.n} is prime. Probability of an error is 1/2${sup('k')}=1/2${sup(this.k)}=${probability}  (${this.k} iterations).`);
    } else {
      this.logger.log(`${this.n} is not prime.`);
    }
    this.logger.log(``);
    return numberIsPrime;
  }

  /**
   * Step 1
   * Get random number for the test
   * [2 ... n-1]
   */
  getRandomNumber() {
    return getRandomNumber(2, this.n - 1);
  }

  /**
   * Step 2
   * Calculate R
   * r = (a ^ n-1 ) mod n
   */
  calculateR(randomNumber: number): number {
    const largePowerModulo = new LargePowerModulo(randomNumber, this.n - 1, this.n);
    largePowerModulo.logger = this.logger;
    const results = largePowerModulo.printResults();

    return results[0];
  }

  /**
   * Step 3
   */
  isComposite(r: number): boolean {
    return r !== 1;
  }
}

