
import { LoggerType } from '../types/logger.type';
import {
  integerDivision,
  modulo,
} from '../utility';
import { logger } from './logger';



/**
  * Exrended Euclidean Algorithm
  *
  * Returns
  * a (GCD)
  * x2  
  * y2 a⁻¹ - В случае если первое число равно 1, третье число является обратным по умножению числу b по модулю a
  *  
 **/
export class EuclideanAlgorithm {

  private _q: (number | null)[] = [];
  private _r: (number | null)[] = [];

  private _x: (number | null)[] = [];
  private _y: (number | null)[] = [];

  private _a: (number | null)[] = [];
  private _b: (number | null)[] = [];

  private _x2: (number | null)[] = [];
  private _x1: (number | null)[] = [];
  private _y2: (number | null)[] = [];
  private _y1: (number | null)[] = [];

  private _currentRow: number = -1;

  // allows to use a customer logger
  logger: LoggerType = logger;

  init(a: number, b: number) {
    this.addRow();
    this.a = a;
    this.b = b;

    this.initA = a;
    this.initB = b;

    this.x2 = 1;
    this.x1 = 0;
    this.y2 = 0;
    this.y1 = 1;

  }

  addRow() {
    this._currentRow = this._q.length;

    this._q.push(null);
    this._r.push(null);

    this._x.push(null);
    this._y.push(null);

    this._a.push(null);
    this._b.push(null);

    this._x2.push(null);
    this._x1.push(null);
    this._y2.push(null);
    this._y1.push(null);

  }


  next() {
    this.addRow();

    this.q = integerDivision(this.aPrev, this.bPrev);
    this.r = modulo(this.aPrev, this.bPrev);

    this.x = this.x2Prev - this.q * this.x1Prev;
    this.y = this.y2Prev - this.q * this.y1Prev;

    this.a = this.bPrev;
    this.b = this.r;

    this.x2 = this.x1Prev;
    this.x1 = this.x;
    this.y2 = this.y1Prev;
    this.y1 = this.y;

  }



  // ====================================



  set q(q: number) {
    this._q[this._currentRow] = q;
  }
  set r(r: number) {
    this._r[this._currentRow] = r;
  }


  set x(x: number) {
    this._x[this._currentRow] = x;
  }
  set y(y: number) {
    this._y[this._currentRow] = y;
  }


  set a(a: number) {
    this._a[this._currentRow] = a;
  }
  set b(b: number) {
    this._b[this._currentRow] = b;
  }


  set x2(x2: number) {
    this._x2[this._currentRow] = x2;
  }
  set x1(x1: number) {
    this._x1[this._currentRow] = x1;
  }
  set y2(y2: number) {
    this._y2[this._currentRow] = y2;
  }
  set y1(y1: number) {
    this._y1[this._currentRow] = y1;
  }




  // ====================================

  get q(): number {
    return this._q[this._currentRow] ?? 0;
  }
  get r(): number {
    return this._r[this._currentRow] ?? 0;
  }


  get x(): number {
    return this._x[this._currentRow] ?? 0;
  }
  get y(): number {
    return this._y[this._currentRow] ?? 0;
  }


  get a(): number {
    return this._a[this._currentRow] ?? 0;
  }
  get b(): number {
    return this._b[this._currentRow] ?? 0;
  }


  get x2(): number {
    return this._x2[this._currentRow] ?? 0;
  }
  get x1(): number {
    return this._x1[this._currentRow] ?? 0;
  }
  get y2(): number {
    return this._y2[this._currentRow] ?? 0;
  }
  get y1(): number {
    return this._y1[this._currentRow] ?? 0;
  }



  // ====================================


  get qPrev(): number {
    return this._q[this.prevRow] ?? 0;
  }
  get rPrev(): number {
    return this._r[this.prevRow] ?? 0;
  }


  get xPrev(): number {
    return this._x[this.prevRow] ?? 0;
  }
  get yPrev(): number {
    return this._y[this.prevRow] ?? 0;
  }


  get aPrev(): number {
    return this._a[this.prevRow] ?? 0;
  }
  get bPrev(): number {
    return this._b[this.prevRow] ?? 0;
  }


  get x2Prev(): number {
    return this._x2[this.prevRow] ?? 0;
  }
  get x1Prev(): number {
    return this._x1[this.prevRow] ?? 0;
  }
  get y2Prev(): number {
    return this._y2[this.prevRow] ?? 0;
  }
  get y1Prev(): number {
    return this._y1[this.prevRow] ?? 0;
  }

  initA: number = 0;
  initB: number = 0;

  // ====================================
  constructor(a?: number, b?: number) {
    if (typeof a === 'number') {
      this.a = a;
      this.initA = a;
    }
    if (typeof b === 'number') {
      this.b = b;
      this.initB = b;
    }
  }



  /**
   * Get rows
   * @returns 
   */
  getRows(): string[] {
    const rows: string[] = [];
    rows.push(`q\tr\tx\ty\ta\tb\tx₂\tx₁\ty₂\ty₁`);
    for (let i = 0; i <= this._currentRow; i++) {
      rows.push(`${this._q[i] ?? ""}\t${this._r[i] ?? ""}\t${this._x[i] ?? ""}\t${this._y[i] ?? ""}\t${this._a[i]}\t${this._b[i]}\t${this._x2[i]}\t${this._x1[i]}\t${this._y2[i]}\t${this._y1[i]}`);
    }
    return rows;
  }

  /**
   * Значения
   * a (GCD)
   * x2  
   * y2 a⁻¹ - В случае если первое число равно 1, третье число является обратным по умножению числу b по модулю a
   * @returns 
   */
  getResult(): [number, number, number] {
    // this.a = d
    // this.x2 = a
    // this.y2 = y
    return [
      this.a,
      this.x2,
      this.y2,
    ];
  }

  get length(): number {
    return this._q.length;
  }

  get prevRow(): number {
    return this._currentRow - 1;
  }


  /**
   * Start calculation
   * @returns 
   */
  calc(a: number | null = null, b: number | null = null): [number, number, number] {

    this.a = a ?? this.a;
    this.b = b ?? this.b;

    let breakOut: number = 100;

    this.init(this.a, this.b);

    while (this.b !== 0) {
      this.next();
      breakOut--;
      if (!breakOut) {
        break;
      }
    }

    return this.getResult();
  }

  /**
   * Print results of the last calculation
   * (calc method must be invoked first)
   */
  printResults(): void {
    this.logger.log(`Таблица Алгоритм Евклида для значений a = ${this.initA}, b = ${this.initB}`);

    const rows = this.getRows();
    rows.forEach((r: string) => {
      this.logger.log(`${r}`, 'color:yellow');
    });

    const result = this.getResult();

    this.logger.log(`НОД: ${result[0]}, ${result[1]}, ${result[2]}`);

  }

}
