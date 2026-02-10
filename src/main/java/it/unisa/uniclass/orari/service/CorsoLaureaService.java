package it.unisa.uniclass.orari.service;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.dao.CorsoLaureaRemote;
import jakarta.ejb.EJB;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;
import java.util.List;

@Stateless
public class CorsoLaureaService {

    @EJB(beanName = "CorsoLaureaDAO")
    private CorsoLaureaRemote corsoLaureaDAO;

    public CorsoLaureaService() {
    }

    public CorsoLaurea trovaCorsoLaurea(long id) {
        try {
            return corsoLaureaDAO.trovaCorsoLaurea(id);
        } catch (NoResultException e) {
            return null;
        }
    }

    public CorsoLaurea trovaCorsoLaurea(String nome) {
        try {
            return corsoLaureaDAO.trovaCorsoLaurea(nome);
        } catch (NoResultException e) {
            return null;
        }
    }

    public List<CorsoLaurea> trovaTutti() {
        try {
            return corsoLaureaDAO.trovaTutti();
        } catch (Exception e) {
            throw new RuntimeException("Errore durante il recupero dei corsi di laurea.", e);
        }
    }

    public void aggiungiCorsoLaurea(CorsoLaurea corsoLaurea) {
        if (corsoLaurea == null || corsoLaurea.getNome() == null || corsoLaurea.getNome().isEmpty()) {
            throw new IllegalArgumentException("Il corso di laurea deve avere un nome valido.");
        }
        corsoLaureaDAO.aggiungiCorsoLaurea(corsoLaurea);
    }

    public void rimuoviCorsoLaurea(CorsoLaurea corsoLaurea) {
        if (corsoLaurea == null) {
            throw new IllegalArgumentException("Il corso di laurea da rimuovere non può essere null.");
        }
        corsoLaureaDAO.rimuoviCorsoLaurea(corsoLaurea);
    }
}