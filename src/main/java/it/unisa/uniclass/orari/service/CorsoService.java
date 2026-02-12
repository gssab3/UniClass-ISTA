package it.unisa.uniclass.orari.service;

import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.service.dao.CorsoRemote;
import jakarta.ejb.EJB;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;
import java.util.List;

@Stateless
public class CorsoService {

    @EJB(beanName = "CorsoDAO")
    private CorsoRemote corsoDao;

    public CorsoService() {}

    // Constructor for testing purposes
    public CorsoService(CorsoRemote corsoDao) {
        this.corsoDao = corsoDao;
    }

    public Corso trovaCorso(long id) {
        try {
            return corsoDao.trovaCorso(id);
        } catch (NoResultException e) {
            return null;
        }
    }

    public List<Corso> trovaCorsiCorsoLaurea(String nomeCorsoLaurea) {
        return corsoDao.trovaCorsiCorsoLaurea(nomeCorsoLaurea);
    }

    public List<Corso> trovaTutti() {
        return corsoDao.trovaTutti();
    }

    public void aggiungiCorso(Corso corso) {
        corsoDao.aggiungiCorso(corso);
    }

    public void rimuoviCorso(Corso corso) {
        corsoDao.rimuoviCorso(corso);
    }
}