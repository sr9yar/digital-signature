import { LoggerType } from '../types/logger.type';


export const logColors = new Map([
  ['bright', '\x1b[1m'],
  ['dim', '\x1b[2m'],
  ['underscore', '\x1b[4m'],
  ['blink', '\x1b[5m'],
  ['reverse', '\x1b[7m'],
  ['hidden', '\x1b[8m'],

  ['black', '\x1b[30m'],
  ['red', '\x1b[31m'],
  ['green', '\x1b[32m'],
  ['yellow', '\x1b[33m'],
  ['blue', '\x1b[34m'],
  ['magenta', '\x1b[35m'],
  ['cyan', '\x1b[36m'],
  ['white', '\x1b[37m'],
  ['gray', '\x1b[90m'],

  ['bgBlack', '\x1b[40m'],
  ['bgRed', '\x1b[41m'],
  ['bgGreen', '\x1b[42m'],
  ['bgYellow', '\x1b[43m'],
  ['bgBlue', '\x1b[44m'],
  ['bgMagenta', '\x1b[45m'],
  ['bgCyan', '\x1b[46m'],
  ['bgWhite', '\x1b[47m'],
  ['bgGray', '\x1b[100m'],
]);

export const closeSymbol = '\x1b[0m';



/**
 * Logger
 */
export class Logger implements LoggerType {

  name: string = `Logger:${Date.now()}`;

  constructor(name?: string) {
    if (name) {
      this.name = name;
    }
  }

  private verboseMode: boolean = true;

  logs: string[] = [];

  /**
   * Write a 'log' level log.

  * @param value 
  * @returns 
  */
  log(message: any, ...optionalParams: any[]): void {
    // let color: any = 'green';
    let color: any = 'white';
    optionalParams ??= [];
    const colorOptionIndex = optionalParams.findIndex((o: any) => o?.toString().startsWith('color:'));
    if (colorOptionIndex !== -1) {
      color = optionalParams[colorOptionIndex].split(':').map((a: string) => a.trim())[1];
      optionalParams.splice(colorOptionIndex, 1);
    }
    optionalParams.pop();
    const messageString = `${message}`;

    this.logs.push(messageString);

    if (!this.verboseMode) {
      return;
    }
    console.log(this.styleText(color, message), ...optionalParams);
  }

  /**
   * Write a 'fatal' level log.
   */
  fatal(message: any, ...optionalParams: any[]) {
    optionalParams.pop();
    if (!this.verboseMode) {
      return;
    }
    console.error(this.styleText('red', message), ...optionalParams);
  }

  /**
   * Write an 'error' level log.
   */
  error(message: any, ...optionalParams: any[]) {
    optionalParams.pop();
    if (!this.verboseMode) {
      return;
    }
    console.error(this.styleText('red', message), ...optionalParams);
  }

  /**
   * Write a 'warn' level log.
   */
  warn(message: any, ...optionalParams: any[]) {
    optionalParams.pop();
    if (!this.verboseMode) {
      return;
    }
    console.warn(this.styleText('cyan', message), ...optionalParams);
  }

  /**
   * Write a 'debug' level log.
   */
  debug?(message: any, ...optionalParams: any[]) {
    optionalParams.pop();
    if (!this.verboseMode) {
      return;
    }
    console.debug(this.styleText('blue', message), ...optionalParams);
  }

  /**
   * Write a 'verbose' level log.
   */
  verbose?(message: any, ...optionalParams: any[]) {
    optionalParams.pop();
    if (!this.verboseMode) {
      return;
    }
    console.debug(this.styleText('blue', message), ...optionalParams);
  }



  /**
   * Set print to console
   * @param value 
   */
  setVerbosity(value: boolean = true): void {
    this.verboseMode = value;
  }
  /**
   * Reset logs
   */
  clearLogs(): void {
    this.logs?.splice(0, this.logs.length);
  }


  /**
   * Color messsage
   * @param color 
   * @param message 
   */
  private styleText(color: string, message: string): string {
    if (logColors.has(color)) {
      return `${logColors.get(color)}${message}${closeSymbol}`;
    }
    return message;
  }
}

export const logger = new Logger();


