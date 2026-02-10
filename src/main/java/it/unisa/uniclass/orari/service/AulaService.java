package it.unisa.uniclass.orari.service;

import it.unisa.uniclass.orari.model.Aula;
import it.unisa.uniclass.orari.service.dao.AulaRemote;
import jakarta.ejb.EJB;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;
import java.util.List;

@Stateless
public class AulaService {

    @EJB(beanName = "AulaDAO")
    private AulaRemote aulaDao;

    public AulaService() {
    }

    public Aula trovaAula(int id) {
        try {
            return aulaDao.trovaAula(id);
        } catch (NoResultException e) {
            return null;
        }
    }

    public Aula trovaAula(String nome) {
        try {
            return aulaDao.trovaAula(nome);
        } catch (NoResultException e) {
            return null;
        }
    }

    public List<Aula> trovaTutte() {
        return aulaDao.trovaTutte();
    }

    public List<Aula> trovaAuleEdificio(String edificio) {
        return aulaDao.trovaAuleEdificio(edificio);
    }

    public List<String> trovaEdifici() {
        return aulaDao.trovaEdifici();
    }

    public void aggiungiAula(Aula aula) {
        if (aula == null) {
            throw new IllegalArgumentException("Argument 'aula' must not be null");
        }
        aulaDao.aggiungiAula(aula);
    }

    public void rimuoviAula(Aula aula) {
        if (aula == null) {
            throw new IllegalArgumentException("Argument 'aula' must not be null");
        }
        aulaDao.rimuoviAula(aula);
    }
}
