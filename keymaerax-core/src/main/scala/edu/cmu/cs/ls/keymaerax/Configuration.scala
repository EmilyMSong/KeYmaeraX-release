/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax

import java.io.{File, PrintWriter}
import java.nio.file.{Files, Paths}

import org.apache.commons.configuration2.PropertiesConfiguration

import scala.collection.JavaConverters._

/** The KeYmaera X configuration.
  * The purpose of this object is to have a central place for system configuration options of KeYmaera X.
  * @see [[edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX]] */
object Configuration {
  /** Configuration keys */
  object Keys {
    val DB_PATH = "DB_PATH"
    val DEBUG = "DEBUG"
    val GUEST_USER = "GUEST_USER"
    val HOST = "HOST"
    val IS_HOSTED = "IS_HOSTED"
    val DEFAULT_USER = "DEFAULT_USER"
    val USE_DEFAULT_USER = "USE_DEFAULT_USER"
    val JKS = "JKS"
    val MATHEMATICA_LINK_NAME = "MATHEMATICA_LINK_NAME"
    val MATHEMATICA_JLINK_LIB_DIR = "MATHEMATICA_JLINK_LIB_DIR"
    val MATH_LINK_TCPIP = "MATH_LINK_TCPIP"
    val WOLFRAMENGINE_LINK_NAME = "WOLFRAMENGINE_LINK_NAME"
    val WOLFRAMENGINE_JLINK_LIB_DIR = "WOLFRAMENGINE_JLINK_LIB_DIR"
    val WOLFRAMENGINE_TCPIP = "WOLFRAMENGINE_TCPIP"
    val LAX = "LAX"
    val LEMMA_COMPATIBILITY = "LEMMA_COMPATIBILITY"
    val LEMMA_CACHE_PATH = "LEMMA_CACHE_PATH"
    val LOG_ALL_FO = "LOG_ALL_FO"
    val LOG_QE = "LOG_QE"
    val LOG_QE_DURATION = "LOG_QE_DURATION"
    val LOG_QE_STDOUT = "LOG_QE_STDOUT"
    val POLYA_PATH = "POLYA_PATH"
    val PORT = "PORT"
    val PROOF_TERM = "PROOF_TERM"
    val QE_LOG_PATH = "QE_LOG_PATH"
    val QE_TOOL = "QE_TOOL"
    val CEX_SEARCH_DURATION = "CEX_SEARCH_DURATION"
    val MATHEMATICA_QE_METHOD = "QE_METHOD"
    val SMT_CACHE_PATH = "SMT_CACHE_PATH"
    val TEST_DB_PATH = "TEST_DB_PATH"
    val PEGASUS_PATH = "PEGASUS_PATH"
    val PEGASUS_MAIN_FILE = "PEGASUS_MAIN_FILE"
    val Z3_PATH = "Z3_PATH"
    val QE_TIMEOUT_INITIAL = "QE_TIMEOUT_INITIAL"
    val QE_TIMEOUT_CEX = "QE_TIMEOUT_CEX"
    val QE_TIMEOUT_MAX = "QE_TIMEOUT_MAX"
    val QE_ALLOW_INTERPRETED_FNS = "QE_ALLOW_INTERPRETED_FNS"
    val ODE_TIMEOUT_FINALQE = "ODE_TIMEOUT_FINALQE"
    val PEGASUS_INVGEN_TIMEOUT = "PEGASUS_INVGEN_TIMEOUT"
    val PEGASUS_INVCHECK_TIMEOUT = "PEGASUS_INVCHECK_TIMEOUT"
    val PEGASUS_SANITY_TIMEOUT = "PEGASUS_SANITY_TIMEOUT"
    val MATHEMATICA_MEMORY_LIMIT = "MATHEMATICA_MEMORY_LIMIT"
  }

  private val KEYMAERAX_HOME: String = System.getProperty("KEYMAERAX_HOME", ".keymaerax")
  /** The user's home directory for the storage of KeYmaera X configuration and model and proof database files */
  val KEYMAERAX_HOME_PATH: String = System.getProperty("user.home") + File.separator + KEYMAERAX_HOME

  private val CONFIG_PATH: String = System.getProperty("CONFIG_PATH",
    KEYMAERAX_HOME_PATH + File.separator + "keymaerax.conf")
  private val DEFAULT_CONFIG_PATH: String = "/default.conf"

  //@note initializes the home directory
  {
    new File(KEYMAERAX_HOME_PATH).mkdirs()
  }

  /** Reads the configuration (initializes from bundled default configuration if necessary). */
  private val config = {
    val config = new PropertiesConfiguration()
    if (!Files.exists(Paths.get(CONFIG_PATH))) {
      config.read(scala.io.Source.fromInputStream(getClass.getResourceAsStream(DEFAULT_CONFIG_PATH)).reader)
      config.write(new PrintWriter(new File(CONFIG_PATH)))
    } else config.read(scala.io.Source.fromFile(CONFIG_PATH).reader)
    updateConfig(config)
  }

  /** Indicates whether or not the configuration contains the `key`. */
  def contains(key: String): Boolean = config.containsKey(key)

  /** Returns the value of `key`. */
  def apply(key: String): String = config.getString(key)

  /** Returns the value of `key` or None, if not present. */
  def getOption(key: String): Option[String] = if (contains(key)) Some(apply(key)) else None

  /** Returns the configuration entry `key` as an absolute path with file separators. */
  def path(key: String): String = {
    val p = config.getString(key).replaceAllLiterally("/", File.separator)
    if (p.startsWith(File.separator)) p
    else System.getProperty("user.home") + File.separator + p
  }

  /** Sets the `value` of `key` and stores the configuration file (unless !`saveToFile`). */
  def set(key: String, value: String, saveToFile: Boolean = true): Unit = {
    config.setProperty(key, value)
    if (saveToFile) config.write(new PrintWriter(new File(CONFIG_PATH)))
  }

  /** Removes a configuration element and stores the configuration file (unless !`saveToFile`). */
  def remove(key: String, saveToFile: Boolean = true): Unit = {
    config.clearProperty(key)
    if (saveToFile) config.write(new PrintWriter(new File(CONFIG_PATH)))
  }

  private def updateConfig(config: PropertiesConfiguration): PropertiesConfiguration = {
    val default = new PropertiesConfiguration()
    default.read(scala.io.Source.fromInputStream(getClass.getResourceAsStream(DEFAULT_CONFIG_PATH)).reader)
    val missing = default.getKeys().asScala.toSet -- config.getKeys().asScala.toSet
    if (missing.nonEmpty) {
      missing.foreach(m => config.setProperty(m, default.getString(m)))
      if (missing.contains(Configuration.Keys.USE_DEFAULT_USER) && missing.contains(Configuration.Keys.DEFAULT_USER)) {
        // update from a version without default login functionality -> set USE_DEFAULT_USER = "ask"
        config.setProperty(Configuration.Keys.USE_DEFAULT_USER, "ask")
      }
      config.write(new PrintWriter(new File(CONFIG_PATH)))
    }
    config
  }
}
