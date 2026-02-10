package it.unisa.uniclass.orari.service.dao;

import it.unisa.uniclass.orari.model.Giorno;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.ejb.Stateless;
import jakarta.persistence.EntityManager;
import jakarta.persistence.PersistenceContext;
import jakarta.persistence.TypedQuery;
import java.sql.Time;
import java.util.ArrayList;
import java.util.List;

@Stateless(name = "LezioneDAO")
public class LezioneDAO implements LezioneRemote {

    @PersistenceContext(unitName = "DBUniClassPU")
    private EntityManager em;

    @Override
    public Lezione trovaLezione(long id) {
        return em.find(Lezione.class, id);
    }

    @Override
    public List<Lezione> trovaLezioniCorso(String nomeCorso) {
        return em.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO, Lezione.class)
                .setParameter("nomeCorso", nomeCorso)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaLezioniOre(Time oraInizio, Time oraFine) {
        return em.createNamedQuery(Lezione.TROVA_LEZIONE_ORE, Lezione.class)
                .setParameter("oraInizio", oraInizio)
                .setParameter("oraFine", oraFine)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaLezioniOreGiorno(Time oraInizio, Time oraFine, Giorno giorno) {
        return em.createNamedQuery(Lezione.TROVA_LEZIONE_ORE_GIORNO, Lezione.class)
                .setParameter("oraInizio", oraInizio)
                .setParameter("oraFine", oraFine)
                .setParameter("giorno", giorno)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaLezioniAule(String nome) {
        return em.createNamedQuery(Lezione.TROVA_LEZIONE_AULA, Lezione.class)
                .setParameter("nome", nome)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaTutte() {
        return em.createNamedQuery(Lezione.TROVA_TUTTE, Lezione.class).getResultList();
    }

    @Override
    public List<Lezione> trovaLezioniCorsoLaureaRestoAnno(long clid, long rid, int annoid) {
        return em.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO, Lezione.class)
                .setParameter("corsoLaureaId", clid)
                .setParameter("restoId", rid)
                .setParameter("annoId", annoid)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaLezioniCorsoLaureaRestoAnnoSemestre(long clid, long rid, int annoid, int semestre) {
        return em.createNamedQuery(Lezione.TROVA_LEZIONE_CORSO_RESTO_ANNO_SEMESTRE, Lezione.class)
                .setParameter("corsoLaureaId", clid)
                .setParameter("restoId", rid)
                .setParameter("annoId", annoid)
                .setParameter("semestre", semestre)
                .getResultList();
    }

    @Override
    public List<Lezione> trovaLezioniDocente(String nomeDocente) {
        return em.createNamedQuery(Lezione.TROVA_LEZIONI_DOCENTE, Lezione.class)
                .setParameter("nomeDocente", nomeDocente)
                .getResultList();
    }

    @Override
    public void aggiungiLezione(Lezione lezione) {
        em.persist(lezione);
    }

    @Override
    public void rimuoviLezione(Lezione lezione) {
        // FIX: Aggiornato getter da getDocenti() a getAccademici()
        if (lezione.getAccademici() != null) {
            for (Accademico a : lezione.getAccademici()) {
                a.getLezioni().remove(lezione);
                em.merge(a);
            }
        }
        em.remove(em.contains(lezione) ? lezione : em.merge(lezione));
    }
}