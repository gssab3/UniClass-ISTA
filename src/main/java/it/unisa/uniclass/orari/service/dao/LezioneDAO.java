package it.unisa.uniclass.orari.service.dao;

import it.unisa.uniclass.orari.model.Giorno;
import it.unisa.uniclass.orari.model.Lezione;
import jakarta.ejb.Stateless;
import jakarta.persistence.EntityManager;
import jakarta.persistence.PersistenceContext;
import jakarta.persistence.TypedQuery;
import java.sql.Time;
import java.util.List;

@Stateless(name = "LezioneDAO")
public class LezioneDAO implements LezioneRemote {

    // Campo richiesto dai test
    @PersistenceContext(unitName = "DBUniClassPU")
    public EntityManager emUniClass;

    @Override
    public Lezione trovaLezione(long id) {
        return emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE, Lezione.class)
                .setParameter("id", id)
                .getSingleResult();
    }

    @Override
    public List<Lezione> trovaLezioniCorso(String nomeCorso) {
        return emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO, Lezione.class)
                .setParameter("nomeCorso", nomeCorso)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaLezioniOre(Time oraInizio, Time oraFine) {
        return emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_ORE, Lezione.class)
                .setParameter("oraInizio", oraInizio)
                .setParameter("oraFine", oraFine)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaLezioniOreGiorno(Time oraInizio, Time oraFine, Giorno giorno) {
        return emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_ORE, Lezione.class)
                .setParameter("oraInizio", oraInizio)
                .setParameter("oraFine", oraFine)
                .setParameter("giorno", giorno)
                .getResultList();
    }


    @Override
    public List<Lezione> trovaLezioniAule(String nome) {
        return emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_AULA, Lezione.class)
                .setParameter("nome", nome)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaTutte() {
        return emUniClass.createNamedQuery(Lezione.TROVA_TUTTE, Lezione.class)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaLezioniCorsoLaureaRestoAnno(long clid, long rid, int annoid) {
        return emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO, Lezione.class)
                .setParameter("corsoLaureaId", clid)
                .setParameter("restoId", rid)
                .setParameter("annoId", annoid)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaLezioniCorsoLaureaRestoAnnoSemestre(long clid, long rid, int annoid, int semestre) {
        return emUniClass.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO_SEMESTRE, Lezione.class)
                .setParameter("corsoLaureaId", clid)
                .setParameter("restoId", rid)
                .setParameter("annoId", annoid)
                .setParameter("semestre", semestre)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaLezioniDocente(String nomeDocente) {
        return emUniClass.createNamedQuery(Lezione.TROVA_LEZIONI_DOCENTE, Lezione.class)
                .setParameter("nomeDocente", nomeDocente)
                .getResultList();
    }

    @Override
    public void aggiungiLezione(Lezione lezione) {
        emUniClass.merge(lezione); // richiesto dai test
    }

    @Override
    public void rimuoviLezione(Lezione lezione) {
        emUniClass.remove(lezione); // richiesto dai test
    }
}
