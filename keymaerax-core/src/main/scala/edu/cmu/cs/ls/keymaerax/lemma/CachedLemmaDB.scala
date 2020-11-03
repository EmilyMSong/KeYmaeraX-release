/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * @note Code Review 2016-08-16
  */
package edu.cmu.cs.ls.keymaerax.lemma

import edu.cmu.cs.ls.keymaerax.Logging

import scala.collection.mutable

/**
  * Extends an arbitrary LemmaDB with caching functionality
  * to reduce the cost of repeated accesses to the same Lemma
  * within a given KeYmaeraX session.
  *
  * Created by bbohrer on 8/3/16.
  */
class CachedLemmaDB(db: LemmaDB) extends LemmaDB with Logging {
  /** The lemma cache, updated lazily on access of a lemma. */
  private var cachedLemmas: mutable.Map[LemmaID, Lemma] = mutable.Map()

  /** @inheritdoc */
  final override def contains(lemmaID: LemmaID): Boolean = cachedLemmas.keySet.contains(lemmaID) || db.contains(lemmaID)

  /** @inheritdoc */
  final override def get(lemmaIDs: List[LemmaID]): Option[List[Lemma]] = {
    /* Get as many lemmas as possible from the cache */
    val (cached, uncached) = lemmaIDs.zipWithIndex.partition{case (x,_) => cachedLemmas.contains(x)}
    val fromCache = cached.map({ case (x, i) => (cachedLemmas(x), i) })
    val (uncachedIDs, uncachedIdxs) = uncached.unzip
    /* Use a single get() call for performance when getting uncached lemmas */
    try {
      val fromDB = db.get(uncachedIDs).map(_.zip(uncachedIdxs))
      fromDB.map(list => {
        cachedLemmas ++= fromCache.map({ case (lemma, idx) => (lemmaIDs(idx), lemma) })
        /* Preserve original order when combining cached vs. uncached lemmas*/
        (list ::: fromCache).sortWith({ case ((_, i), (_, j)) => i < j }).map(_._1)
      })
    } catch {
      case e: Throwable =>
        logger.error("Error while trying to retrieve lemma", e)
        None
    }
  }

  /** @inheritdoc */
  final override def add(lemma: Lemma): LemmaID = {
    val id = db.add(lemma)
    cachedLemmas += ((id,lemma))
    id
  }

  /** @inheritdoc */
  final override def deleteDatabase(): Unit = {
    cachedLemmas.clear()
    db.deleteDatabase()
  }

  /** @inheritdoc */
  final override def remove(id: LemmaID): Unit = {
    cachedLemmas -= id
    db.remove(id)
  }

  /** @inheritdoc */
  final override def removeAll(folderName: LemmaID): Unit = {
    val remove = cachedLemmas.filter(_._1.startsWith(folderName)).keys
    cachedLemmas --= remove
    db.removeAll(folderName)
  }

  /** @inheritdoc */
  final override def version(): String = db.version()
}
