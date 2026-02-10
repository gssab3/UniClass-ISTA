package it.unisa.uniclass.orari.service;

import it.unisa.uniclass.orari.model.Giorno;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.service.dao.LezioneRemote;
import jakarta.ejb.EJB;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;
import java.sql.Time;
import java.util.List;

@Stateless
public class LezioneService {

    @EJB(beanName = "LezioneDAO")
    private LezioneRemote lezioneDao;

    public LezioneService() {
    }

    public Lezione trovaLezione(long id) {
        try {
            return lezioneDao.trovaLezione(id);
        } catch (NoResultException e) {
            return null;
        }
    }

    public List<Lezione> trovaLezioniCorso(String nomeCorso) {
        return lezioneDao.trovaLezioniCorso(nomeCorso);
    }

    public List<Lezione> trovaLezioniOre(Time oraInizio, Time oraFine) {
        return lezioneDao.trovaLezioniOre(oraInizio, oraFine);
    }

    public List<Lezione> trovaLezioniOreGiorno(Time oraInizio, Time oraFine, Giorno giorno) {
        return lezioneDao.trovaLezioniOreGiorno(oraInizio, oraFine, giorno);
    }

    public List<Lezione> trovaLezioniAule(String nome) {
        return lezioneDao.trovaLezioniAule(nome);
    }

    public List<Lezione> trovaTutte() {
        return lezioneDao.trovaTutte();
    }

    public List<Lezione> trovaLezioniCorsoLaureaRestoAnno(long clid, long rid, int annoid) {
        return lezioneDao.trovaLezioniCorsoLaureaRestoAnno(clid, rid, annoid);
    }

    public List<Lezione> trovaLezioniCorsoLaureaRestoAnnoSemestre(long clid, long rid, int annoid, int semestre) {
        return lezioneDao.trovaLezioniCorsoLaureaRestoAnnoSemestre(clid, rid, annoid, semestre);
    }

    /**
     * Cerca le lezioni in base al nome del docente (ora Accademico).
     * Assicurarsi che la NamedQuery in Lezione.java punti al campo 'accademici'.
     */
    public List<Lezione> trovaLezioniDocente(String nomeDocente) {
        return lezioneDao.trovaLezioniDocente(nomeDocente);
    }

    public void aggiungiLezione(Lezione lezione) {
        lezioneDao.aggiungiLezione(lezione);
    }

    public void rimuoviLezione(Lezione lezione) {
        lezioneDao.rimuoviLezione(lezione);
    }
}