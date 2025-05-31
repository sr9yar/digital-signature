import { LoggerType } from '../lib/types/logger.type';
import { logger } from '../lib/classes/logger';



/**
 * Abstract class 
 */
export abstract class DigitalSignature {

  // Encryption method
  abstract sign(): string;
  // Decryption method
  abstract verify(): boolean;

  logger?: LoggerType = logger;

  /**
   * Set print to console
   * @param value 
   */
  setVerbose(value: boolean): void {
    this.logger?.setVerbosity(value);
  }

  /**
   * Print a log
   * @param value 
   * @returns 
   */
  log(message: any, ...optionalParams: any[]): void {
    this.logger?.log(message, ...optionalParams);
  }

  /**
   * Print a warn
   * @param value 
   * @returns 
   */
  warn(message: any): void {
    this.logger?.warn(message);
  }


  /**
   * Reset logs
   */
  clearLogs(): void {
    this.logger?.clearLogs();
  }

}